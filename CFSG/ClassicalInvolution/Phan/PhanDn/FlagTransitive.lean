module

public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagGeom
public import CFSG.LieType.CurtisTits.TitsGeometry
import all CFSG.ClassicalInvolution.Phan.PhanDn.ChamberMoves
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipFrame

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits
open QuadraticMap CFSG.LieType.Universal.Spin

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {σ : K ≃+* K}
variable {m : ℕ}

private theorem fgt_flagTyp_of_not_solid {U : FlagVert σ m}
    (hU : Module.finrank K U.1 ≠ m + 1) :
    flagTyp U = ⟨Module.finrank K U.1 - 1, by
      have hle := IsFlipflopSub.finrank_le U.2.1
      omega⟩ := by
  unfold flagTyp
  rw [if_neg hU]
  apply Fin.ext
  exact min_eq_left (by
    have hle := IsFlipflopSub.finrank_le U.2.1
    omega)

private theorem fgt_flagTyp_of_solid {U : FlagVert σ m}
    (hU : Module.finrank K U.1 = m + 1) :
    flagTyp U = if Even ((m + 1) - Module.finrank K ↥(U.1 ⊓ stdLag (m + 1) K)) then
      Fin.last m else ⟨m - 1, by omega⟩ := by
  unfold flagTyp
  rw [if_pos hU]

private theorem fgt_flagTyp_ne_of_lt {U W : FlagVert σ m} (h : U.1 < W.1) :
    flagTyp U ≠ flagTyp W := by
  have hfin : Module.finrank K U.1 < Module.finrank K W.1 :=
    Submodule.finrank_lt_finrank_of_lt h
  have hUpos : 1 ≤ Module.finrank K U.1 :=
    Submodule.one_le_finrank_iff.mpr U.2.2.1
  have hWpos : 1 ≤ Module.finrank K W.1 :=
    Submodule.one_le_finrank_iff.mpr W.2.2.1
  have hUle := IsFlipflopSub.finrank_le U.2.1
  have hWle := IsFlipflopSub.finrank_le W.2.1
  have hUne : Module.finrank K U.1 ≠ m := U.2.2.2
  have hWne : Module.finrank K W.1 ≠ m := W.2.2.2
  by_cases hWs : Module.finrank K W.1 = m + 1
  · have hUs : Module.finrank K U.1 ≠ m + 1 := by omega
    rw [fgt_flagTyp_of_not_solid hUs, fgt_flagTyp_of_solid hWs]
    by_cases hE : Even ((m + 1) - Module.finrank K ↥(W.1 ⊓ stdLag (m + 1) K))
    · rw [if_pos hE]
      intro heq
      have hval := congrArg Fin.val heq
      have hlast : ((Fin.last m : Fin (m + 1)) : ℕ) = m := Fin.val_last m
      simp only at hval
      omega
    · rw [if_neg hE]
      intro heq
      have hval := congrArg Fin.val heq
      have hlast : ((Fin.last m : Fin (m + 1)) : ℕ) = m := Fin.val_last m
      simp only at hval
      omega
  · have hUs : Module.finrank K U.1 ≠ m + 1 := by omega
    rw [fgt_flagTyp_of_not_solid hUs, fgt_flagTyp_of_not_solid hWs]
    intro heq
    have hval := congrArg Fin.val heq
    simp only at hval
    omega

theorem flagTyp_ne_of_adj (hσ : ∀ x, σ (σ x) = x) (hm : 1 ≤ m) {U W : FlagVert σ m}
    (h : (flagGraph σ m).Adj U W) : flagTyp U ≠ flagTyp W := by
  rcases h with hlt | hlt | ⟨hU, hW, hInf⟩
  · exact fgt_flagTyp_ne_of_lt hlt
  · exact (fgt_flagTyp_ne_of_lt hlt).symm
  · have hUL : (quadPlusForm (m + 1) K).IsLagrangian U.1 :=
      IsSolid.isLagrangian ⟨U.2.1, hU⟩
    have hWL : (quadPlusForm (m + 1) K).IsLagrangian W.1 :=
      IsSolid.isLagrangian ⟨W.2.1, hW⟩
    have hX : IsFlipflopSub σ (U.1 ⊓ W.1) :=
      isFlipflopSub_inf_of_isLagrangian hσ U.2.1 hUL W.2.1 hWL (by omega)
    have hXdim : Module.finrank K ↥(U.1 ⊓ W.1) + 1 = m + 1 := by omega
    obtain ⟨M, M', -, -, -, -, hev, hodd, huniq⟩ :=
      IsFlipflopSub.exists_two_solids hσ hX hXdim
    have hUeq : U.1 = M ∨ U.1 = M' := huniq U.1 hUL inf_le_left
    have hWeq : W.1 = M ∨ W.1 = M' := huniq W.1 hWL inf_le_right
    have hUW : U.1 ≠ W.1 := by
      intro hEq
      have hc : Module.finrank K ↥(U.1 ⊓ W.1) = m + 1 := by
        rw [hEq, inf_idem, hW]
      omega
    have hpar : Even ((m + 1) - Module.finrank K ↥(U.1 ⊓ stdLag (m + 1) K)) ↔
        ¬ Even ((m + 1) - Module.finrank K ↥(W.1 ⊓ stdLag (m + 1) K)) := by
      rcases hUeq with hUM | hUM' <;> rcases hWeq with hWM | hWM'
      · exact absurd (hUM.trans hWM.symm) hUW
      · rw [hUM, hWM']
        exact ⟨fun _ => hodd, fun _ => hev⟩
      · rw [hUM', hWM]
        exact ⟨fun h _ => hodd h, fun h => absurd hev h⟩
      · exact absurd (hUM'.trans hWM'.symm) hUW
    rw [fgt_flagTyp_of_solid hU, fgt_flagTyp_of_solid hW]
    by_cases hE : Even ((m + 1) - Module.finrank K ↥(U.1 ⊓ stdLag (m + 1) K))
    · rw [if_pos hE, if_neg (hpar.mp hE)]
      intro heq
      have hval := congrArg Fin.val heq
      have hlast : ((Fin.last m : Fin (m + 1)) : ℕ) = m := Fin.val_last m
      simp only at hval
      omega
    · rw [if_neg hE, if_pos (by by_contra h; exact hE (hpar.mpr h))]
      intro heq
      have hval := congrArg Fin.val heq
      have hlast : ((Fin.last m : Fin (m + 1)) : ℕ) = m := Fin.val_last m
      simp only at hval
      omega

theorem flagTyp_smul [CharP K 2] (E : QuadExt F K σ)
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) (U : FlagVert σ m) :
    flagTyp (g • U) = flagTyp U := by
  have hfin : Module.finrank K (g • U).1 = Module.finrank K U.1 := by
    rw [coe_smul_flagVert E g U]
    exact finrank_map_bcLin E (m + 1) g U.1
  by_cases hU : Module.finrank K U.1 = m + 1
  · have hgU : Module.finrank K (g • U).1 = m + 1 := by rw [hfin]; exact hU
    rw [fgt_flagTyp_of_solid hU, fgt_flagTyp_of_solid hgU]
    have hL : (quadPlusForm (m + 1) K).IsLagrangian U.1 :=
      IsSolid.isLagrangian ⟨U.2.1, hU⟩
    have hiff := even_ruling_map_iff E (m + 1)
      (orthDerived_le_rulingGroup E (m + 1) g.2) hL
    rw [coe_smul_flagVert]
    by_cases hE : Even ((m + 1) - Module.finrank K ↥(U.1 ⊓ stdLag (m + 1) K))
    · rw [if_pos (hiff.mpr hE), if_pos hE]
    · rw [if_neg (fun h => hE (hiff.mp h)), if_neg hE]
  · have hgU : Module.finrank K (g • U).1 ≠ m + 1 := by rw [hfin]; exact hU
    rw [fgt_flagTyp_of_not_solid hU, fgt_flagTyp_of_not_solid hgU]
    apply Fin.ext
    show Module.finrank K (g • U).1 - 1 = Module.finrank K U.1 - 1
    rw [hfin]

private theorem fgt_bcLin_injective [CharP K 2] (E : QuadExt F K σ) (n : ℕ)
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n))) :
    Function.Injective (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))) := by
  have hbc : bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)) =
      (bc E n (g : (Fin n → K) ≃ₗ[F] (Fin n → K)) :
        (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) := by
    simpa using bcLin_eq_coe_bc E n (g : (Fin n → K) ≃ₗ[F] (Fin n → K))
  rw [hbc]
  exact (bc E n (g : (Fin n → K) ≃ₗ[F] (Fin n → K))).injective

theorem flagGraph_adj_smul [CharP K 2] (E : QuadExt F K σ)
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) {U W : FlagVert σ m}
    (h : (flagGraph σ m).Adj U W) : (flagGraph σ m).Adj (g • U) (g • W) := by
  have hinj := fgt_bcLin_injective E (m + 1) g
  change (g • U).1 < (g • W).1 ∨ (g • W).1 < (g • U).1 ∨
    (Module.finrank K (g • U).1 = m + 1 ∧ Module.finrank K (g • W).1 = m + 1 ∧
      Module.finrank K ↥((g • U).1 ⊓ (g • W).1) = m)
  rw [coe_smul_flagVert E g U, coe_smul_flagVert E g W]
  rcases h with hlt | hlt | ⟨hU, hW, hInf⟩
  · exact Or.inl ((Submodule.map_lt_map_iff_of_injective hinj).mpr hlt)
  · exact Or.inr (Or.inl ((Submodule.map_lt_map_iff_of_injective hinj).mpr hlt))
  · refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
    · rw [finrank_map_bcLin]
      exact hU
    · rw [finrank_map_bcLin]
      exact hW
    · rw [← Submodule.map_inf (bcLin E (m + 1)
        (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) hinj, finrank_map_bcLin]
      exact hInf

private theorem fgt_polar_eq_zero_of_total {A : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    (hA : ∀ a ∈ A, quadPlus (m + 1) K a = 0) {a b : Fin (m + 1) ⊕ Fin (m + 1) → K}
    (ha : a ∈ A) (hb : b ∈ A) : polar (quadPlus (m + 1) K) a b = 0 := by
  have h := QuadraticMap.map_add (quadPlus (m + 1) K) a b
  rw [hA (a + b) (A.add_mem ha hb), hA a ha, hA b hb] at h
  simpa using h.symm

private def fgtOrthonormal (σ : K ≃+* K) {k : ℕ}
    (w : Fin k → (Fin (m + 1) ⊕ Fin (m + 1) → K)) : Prop :=
  (∀ i, quadPlus (m + 1) K (w i) = 0) ∧
    (∀ i j, polar (quadPlus (m + 1) K) (w i) (w j) = 0) ∧
      (∀ i j, flipHerm σ (w i) (w j) = if i = j then 1 else 0)

private def fgtSpan {k : ℕ} (w : Fin k → (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (d : ℕ) : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
  Submodule.span K (w '' {i : Fin k | (i : ℕ) < d})

omit [Field K] in
private theorem fgt_append_val_lt {k l : ℕ}
    (u : Fin k → (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (v : Fin l → (Fin (m + 1) ⊕ Fin (m + 1) → K)) (i : Fin (k + l))
    (hi : (i : ℕ) < k) : Fin.append u v i = u ⟨(i : ℕ), hi⟩ := by
  have h : i = Fin.castAdd l ⟨(i : ℕ), hi⟩ := Fin.ext (by simp)
  exact (congrArg (Fin.append u v) h).trans (Fin.append_left u v ⟨(i : ℕ), hi⟩)

omit [Field K] in
private theorem fgt_append_val_ge {k l : ℕ}
    (u : Fin k → (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (v : Fin l → (Fin (m + 1) ⊕ Fin (m + 1) → K)) (i : Fin (k + l))
    (hi : k ≤ (i : ℕ)) :
    Fin.append u v i = v ⟨(i : ℕ) - k, by have := i.is_lt; omega⟩ := by
  have hlt : (i : ℕ) - k < l := by have := i.is_lt; omega
  have h : i = Fin.natAdd k ⟨(i : ℕ) - k, hlt⟩ := by
    apply Fin.ext
    rw [Fin.val_natAdd]
    exact (Nat.add_sub_cancel' hi).symm
  exact (congrArg (Fin.append u v) h).trans
    (Fin.append_right u v ⟨(i : ℕ) - k, hlt⟩)

omit [Field K] in
private theorem fgt_append_range {k l : ℕ}
    (u : Fin k → (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (v : Fin l → (Fin (m + 1) ⊕ Fin (m + 1) → K)) :
    Set.range (Fin.append u v) = Set.range u ∪ Set.range v := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi : (i : ℕ) < k
    · exact Or.inl ⟨⟨(i : ℕ), hi⟩, (fgt_append_val_lt u v i hi).symm⟩
    · refine Or.inr ⟨⟨(i : ℕ) - k, by have := i.is_lt; omega⟩, ?_⟩
      exact (fgt_append_val_ge u v i (by omega)).symm
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · refine ⟨Fin.castAdd l i, ?_⟩
      exact fgt_append_val_lt u v (Fin.castAdd l i) (by simp)
    · refine ⟨Fin.natAdd k j, ?_⟩
      simp

private theorem fgt_span_append_left {k l d : ℕ}
    (u : Fin k → (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (v : Fin l → (Fin (m + 1) ⊕ Fin (m + 1) → K)) (hd : d ≤ k) :
    Submodule.span K ((Fin.append u v) '' {i : Fin (k + l) | (i : ℕ) < d}) =
      Submodule.span K (u '' {i : Fin k | (i : ℕ) < d}) := by
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi' : (i : ℕ) < k := lt_of_lt_of_le hi hd
    refine ⟨⟨(i : ℕ), hi'⟩, hi, ?_⟩
    exact (fgt_append_val_lt u v i hi').symm
  · rintro ⟨i, hi, rfl⟩
    refine ⟨Fin.castAdd l i, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, Fin.val_castAdd]
      exact hi
    · exact fgt_append_val_lt u v (Fin.castAdd l i) (by simp)

private theorem fgt_sup_inf_flipOrth_eq (hσ : ∀ x, σ (σ x) = x) (hne : ∃ c, σ c ≠ c)
    {T C : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    (hT : IsFlipflopSub σ T) (hTC : T ≤ C) :
    T ⊔ (C ⊓ flipOrth σ T) = C := by
  refine le_antisymm (sup_le hTC inf_le_left) ?_
  intro c hc
  have htop : c ∈ T ⊔ flipOrth σ T := by
    rw [sup_flipOrth_eq_top hσ hne hT]
    exact Submodule.mem_top
  obtain ⟨t, ht, u, hu, rfl⟩ := Submodule.mem_sup.mp htop
  have huC : u ∈ C := by
    have hEq : u = (t + u) - t := by abel
    rw [hEq]
    exact C.sub_mem hc (hTC ht)
  exact Submodule.mem_sup.mpr ⟨t, ht, u, ⟨huC, hu⟩, rfl⟩

private theorem fgt_isFlipflopSub_inf_flipOrth (hσ : ∀ x, σ (σ x) = x)
    (hne : ∃ c, σ c ≠ c) {T C : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    (hT : IsFlipflopSub σ T) (hC : IsFlipflopSub σ C) (hTC : T ≤ C) :
    IsFlipflopSub σ (C ⊓ flipOrth σ T) := by
  have hsplit := fgt_sup_inf_flipOrth_eq hσ hne hT hTC
  refine ⟨fun u hu => hC.total u hu.1, ?_⟩
  intro u hu hper
  refine hC.nondeg u hu.1 fun c hc => ?_
  have hc' : c ∈ T ⊔ (C ⊓ flipOrth σ T) := by
    rw [hsplit]
    exact hc
  obtain ⟨t, ht, d, hd, rfl⟩ := Submodule.mem_sup.mp hc'
  rw [flipHerm_add_right, (flipHerm_eq_zero_iff hσ).mp ((mem_flipOrth.mp hu.2) t ht),
    hper d hd, add_zero]

private theorem fgt_finrank_inf_flipOrth (hσ : ∀ x, σ (σ x) = x)
    (hne : ∃ c, σ c ≠ c) {T C : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    (hT : IsFlipflopSub σ T) (hTC : T ≤ C) :
    Module.finrank K ↥(C ⊓ flipOrth σ T) = Module.finrank K C - Module.finrank K T := by
  have hsplit := fgt_sup_inf_flipOrth_eq hσ hne hT hTC
  have hdisj : T ⊓ (C ⊓ flipOrth σ T) = ⊥ := by
    rw [← inf_assoc, inf_eq_left.mpr hTC, inf_flipOrth_eq_bot hσ hT]
  have h := Submodule.finrank_sup_add_finrank_inf_eq T (C ⊓ flipOrth σ T)
  rw [hsplit, hdisj, finrank_bot, add_zero] at h
  omega

private theorem fgtSpan_zero {k : ℕ} (w : Fin k → (Fin (m + 1) ⊕ Fin (m + 1) → K)) :
    fgtSpan w 0 = ⊥ := by
  rw [fgtSpan]
  simp

private theorem fgtSpan_succ {k : ℕ} (w : Fin k → (Fin (m + 1) ⊕ Fin (m + 1) → K))
    {d : ℕ} (hd : d < k) :
    fgtSpan w (d + 1) = fgtSpan w d ⊔ K ∙ w ⟨d, hd⟩ := by
  rw [fgtSpan, fgtSpan]
  have hset : {i : Fin k | (i : ℕ) < d + 1} = {i : Fin k | (i : ℕ) < d} ∪ {⟨d, hd⟩} := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro h
      by_cases hid : (i : ℕ) < d
      · exact Or.inl hid
      · right
        apply Fin.ext
        change (i : ℕ) = d
        omega
    · rintro (h | rfl)
      · omega
      · have hvd : ((⟨d, hd⟩ : Fin k) : ℕ) = d := rfl
        rw [hvd]
        omega
  rw [hset, Set.image_union, Set.image_singleton, Submodule.span_union]

private theorem fgt_sub_eq_fgtSpan (f : FlipFrame σ (m + 1)) (w : Fin m →
    (Fin (m + 1) ⊕ Fin (m + 1) → K))
    (hline : ∀ i : Fin m, f.line i.castSucc = K ∙ w i) :
    ∀ d : ℕ, d ≤ m → f.sub d = fgtSpan w d := by
  intro d hd
  induction d with
  | zero => rw [fgtSpan_zero, FlipFrame.sub_zero]
  | succ d ih =>
    have hdm : d < m := by omega
    rw [FlipFrame.sub_succ f (by omega : d < m + 1), ih (by omega),
      fgtSpan_succ w hdm]
    congr 1
    have hidx : (⟨d, by omega⟩ : Fin (m + 1)) = (⟨d, hdm⟩ : Fin m).castSucc := Fin.ext rfl
    rw [hidx, hline]

private theorem fgt_exists_adapted_basis (hσ : ∀ x, σ (σ x) = x) (hne : ∃ c, σ c ≠ c)
    (hN : ∀ a : K, σ a = a → a ≠ 0 → ∃ x : K, x * σ x = a)
    (A : Finset (FlagVert σ m)) :
    ∀ (k : ℕ) (C : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)),
      IsFlipflopSub σ C → Module.finrank K C = k →
      (∀ x ∈ A, Module.finrank K x.1 ≠ m + 1) →
      (∀ x ∈ A, ∀ y ∈ A, x ≠ y → x.1 < y.1 ∨ y.1 < x.1) →
      (∀ x ∈ A, x.1 ≤ C) →
      ∃ w : Fin k → (Fin (m + 1) ⊕ Fin (m + 1) → K),
        fgtOrthonormal σ w ∧
        (∀ x ∈ A, fgtSpan w (Module.finrank K x.1) = x.1) ∧
        Submodule.span K (Set.range w) = C := by
  classical
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    intro k C hC hCdim hAns hAch hAle
    by_cases hA0 : A.Nonempty
    · obtain ⟨x, hxA, hxmax⟩ :=
        Finset.exists_max_image A (fun y => Module.finrank K y.1) hA0
      let B := A.erase x
      have hBA : B ⊂ A := Finset.erase_ssubset hxA
      have hBns : ∀ y ∈ B, Module.finrank K y.1 ≠ m + 1 := fun y hy =>
        hAns y (Finset.mem_of_mem_erase hy)
      have hBch : ∀ y ∈ B, ∀ z ∈ B, y ≠ z → y.1 < z.1 ∨ z.1 < y.1 := by
        intro y hy z hz hyz
        exact hAch y (Finset.mem_of_mem_erase hy) z (Finset.mem_of_mem_erase hz) hyz
      have hBleC : ∀ y ∈ B, y.1 ≤ C := fun y hy => hAle y (Finset.mem_of_mem_erase hy)
      have hBlex : ∀ y ∈ B, y.1 ≤ x.1 := by
        intro y hy
        have hyA := Finset.mem_of_mem_erase hy
        have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
        rcases hAch y hyA x hxA hyx with h | h
        · exact le_of_lt h
        · exfalso
          have hlt := Submodule.finrank_lt_finrank_of_lt h
          have hle := hxmax y hyA
          omega
      have hxleC : x.1 ≤ C := hAle x hxA
      have hdxk : Module.finrank K x.1 ≤ k := by
        rw [← hCdim]
        exact Submodule.finrank_mono hxleC
      obtain ⟨w', horth', hspan', hrange'⟩ :=
        ih B hBA (Module.finrank K x.1) x.1 x.2.1 rfl hBns hBch hBlex
      let D : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) := C ⊓ flipOrth σ x.1
      have hD : IsFlipflopSub σ D :=
        fgt_isFlipflopSub_inf_flipOrth hσ hne x.2.1 hC hxleC
      have hDdim : Module.finrank K D = k - Module.finrank K x.1 := by
        rw [show D = C ⊓ flipOrth σ x.1 from rfl,
          fgt_finrank_inf_flipOrth hσ hne x.2.1 hxleC, hCdim]
      have hDC : D ≤ C := inf_le_left
      obtain ⟨bD, hbD⟩ := exists_orthonormal_basis hσ hne hN hD
      let BD : Module.Basis (Fin (k - Module.finrank K x.1)) K D :=
        bD.reindex (finCongr hDdim)
      let u : Fin (k - Module.finrank K x.1) →
          (Fin (m + 1) ⊕ Fin (m + 1) → K) := fun i => (BD i : D)
      have hu_orth : ∀ i j, flipHerm σ (u i) (u j) = if i = j then 1 else 0 := by
        intro i j
        rw [show u i = ((BD i : D) : Fin (m + 1) ⊕ Fin (m + 1) → K) from rfl,
          show u j = ((BD j : D) : Fin (m + 1) ⊕ Fin (m + 1) → K) from rfl,
          Module.Basis.reindex_apply, Module.Basis.reindex_apply, hbD]
        simp
      have hu_span : Submodule.span K (Set.range u) = D := by
        have h := congrArg (Submodule.map D.subtype) BD.span_eq
        rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at h
        rw [← h]
        congr 1
        rw [show Set.range u = D.subtype '' Set.range (⇑BD) from Set.range_comp _ _]
      let hlen : k = Module.finrank K x.1 + (k - Module.finrank K x.1) := by omega
      let w : Fin k → (Fin (m + 1) ⊕ Fin (m + 1) → K) := fun i =>
        Fin.append w' u (finCongr hlen i)
      have hwval : ∀ i : Fin k, ((finCongr hlen i : Fin (Module.finrank K x.1 +
          (k - Module.finrank K x.1))) : ℕ) = (i : ℕ) := fun i => by
        rw [finCongr_apply, Fin.val_cast]
      have hw_left : ∀ (i : Fin k) (hi : (i : ℕ) < Module.finrank K x.1),
          w i = w' ⟨(i : ℕ), hi⟩ := by
        intro i hi
        show Fin.append w' u (finCongr hlen i) = _
        rw [fgt_append_val_lt w' u (finCongr hlen i) (by rw [hwval]; exact hi)]
        rfl
      have hw_right : ∀ (i : Fin k) (hi : Module.finrank K x.1 ≤ (i : ℕ)),
          w i = u ⟨(i : ℕ) - Module.finrank K x.1, by have := i.is_lt; omega⟩ := by
        intro i hi
        show Fin.append w' u (finCongr hlen i) = _
        rw [fgt_append_val_ge w' u (finCongr hlen i) (by rw [hwval]; exact hi)]
        rfl
      have hwx : ∀ i : Fin (Module.finrank K x.1),
          w' i ∈ x.1 := fun i => by
        rw [← hrange']
        exact Submodule.subset_span ⟨i, rfl⟩
      have hw : fgtOrthonormal σ w := by
        refine ⟨?_, ?_, ?_⟩
        · intro i
          by_cases hi : (i : ℕ) < Module.finrank K x.1
          · rw [hw_left i hi]
            exact horth'.1 _
          · rw [hw_right i (by omega)]
            exact hD.total _ (BD _).2
        · intro i j
          by_cases hi : (i : ℕ) < Module.finrank K x.1
          · by_cases hj : (j : ℕ) < Module.finrank K x.1
            · rw [hw_left i hi, hw_left j hj]
              exact horth'.2.1 _ _
            · rw [hw_left i hi, hw_right j (by omega)]
              exact fgt_polar_eq_zero_of_total (A := C) hC.total (hxleC (hwx _)) (hDC (BD _).2)
          · by_cases hj : (j : ℕ) < Module.finrank K x.1
            · rw [hw_right i (by omega), hw_left j hj]
              exact fgt_polar_eq_zero_of_total (A := C) hC.total (hDC (BD _).2) (hxleC (hwx _))
            · rw [hw_right i (by omega), hw_right j (by omega)]
              exact fgt_polar_eq_zero_of_total (A := C) hC.total (hDC (BD _).2) (hDC (BD _).2)
        · intro i j
          by_cases hi : (i : ℕ) < Module.finrank K x.1
          · by_cases hj : (j : ℕ) < Module.finrank K x.1
            · rw [hw_left i hi, hw_left j hj, horth'.2.2]
              by_cases h : i = j
              · have hc : (⟨i, hi⟩ : Fin (Module.finrank K x.1)) = ⟨j, hj⟩ := by
                  apply Fin.ext
                  change (i : ℕ) = (j : ℕ)
                  rw [h]
                rw [if_pos hc, if_pos h]
              · rw [if_neg (by
                    intro hh
                    exact h (Fin.ext (by
                      have := congrArg Fin.val hh
                      simpa using this))), if_neg h]
            · rw [hw_left i hi, hw_right j (by omega)]
              rw [if_neg (by omega)]
              exact (mem_flipOrth.mp (BD _).2.2) _ (hwx _)
          · by_cases hj : (j : ℕ) < Module.finrank K x.1
            · rw [hw_right i (by omega), hw_left j hj]
              rw [if_neg (by omega)]
              exact (flipHerm_eq_zero_iff hσ).mp
                ((mem_flipOrth.mp (BD _).2.2) _ (hwx _))
            · rw [hw_right i (by omega), hw_right j (by omega)]
              rw [hu_orth]
              by_cases hij : i = j
              · subst hij
                rw [if_pos rfl, if_pos (by apply Fin.ext; rfl)]
              · rw [if_neg hij, if_neg (by
                  intro h
                  apply hij
                  apply Fin.ext
                  have hval := congrArg Fin.val h
                  simp only at hval
                  omega)]
      have hspanB : ∀ y ∈ B, fgtSpan w (Module.finrank K y.1) = y.1 := by
        intro y hy
        have hyA := Finset.mem_of_mem_erase hy
        have hdyx : Module.finrank K y.1 ≤ Module.finrank K x.1 := hxmax y hyA
        have hdyk : Module.finrank K y.1 ≤ k := by omega
        have hset : w '' {i : Fin k | (i : ℕ) < Module.finrank K y.1} =
            w' '' {i : Fin (Module.finrank K x.1) | (i : ℕ) < Module.finrank K y.1} := by
          ext z
          constructor
          · rintro ⟨i, hi, rfl⟩
            have hidx : (i : ℕ) < Module.finrank K x.1 := lt_of_lt_of_le hi hdyx
            refine ⟨⟨(i : ℕ), hidx⟩, hi, ?_⟩
            rw [hw_left i hidx]
          · rintro ⟨i, hi, rfl⟩
            refine ⟨⟨(i : ℕ), by omega⟩, hi, ?_⟩
            rw [hw_left _ (lt_of_lt_of_le hi hdyx)]
        rw [fgtSpan, hset, ← fgtSpan]
        exact hspan' y hy
      have hspanx : fgtSpan w (Module.finrank K x.1) = x.1 := by
        have hset : w '' {i : Fin k | (i : ℕ) < Module.finrank K x.1} = Set.range w' := by
          ext z
          constructor
          · rintro ⟨i, hi, rfl⟩
            rw [hw_left i hi]
            exact ⟨_, rfl⟩
          · rintro ⟨j, rfl⟩
            refine ⟨⟨(j : ℕ), by omega⟩, ?_, ?_⟩
            · exact j.is_lt
            · rw [hw_left _ j.is_lt]
        rw [fgtSpan, hset, hrange']
      have hspanall : Submodule.span K (Set.range w) = C := by
        have hrange_w : Set.range w = Set.range (Fin.append w' u) := by
          rw [show w = Fin.append w' u ∘ finCongr hlen from rfl, Set.range_comp,
            Set.range_eq_univ.mpr (EquivLike.surjective (finCongr hlen)), Set.image_univ]
        rw [hrange_w, fgt_append_range, Submodule.span_union, hrange', hu_span,
          fgt_sup_inf_flipOrth_eq hσ hne x.2.1 hxleC]
      refine ⟨w, hw, ?_, hspanall⟩
      intro y hy
      by_cases hyx : y = x
      · subst hyx
        exact hspanx
      · exact hspanB y (Finset.mem_erase.mpr ⟨hyx, hy⟩)
    · have hempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA0
      subst hempty
      obtain ⟨b, hb⟩ := exists_orthonormal_basis hσ hne hN hC
      let B : Module.Basis (Fin k) K C := b.reindex (finCongr hCdim)
      let w : Fin k → (Fin (m + 1) ⊕ Fin (m + 1) → K) := fun i => (B i : C)
      have hw : fgtOrthonormal σ w := by
        refine ⟨?_, ?_, ?_⟩
        · intro i
          exact hC.total _ (B i).2
        · intro i j
          exact fgt_polar_eq_zero_of_total (A := C) hC.total (B i).2 (B j).2
        · intro i j
          rw [show w i = ((B i : C) : Fin (m + 1) ⊕ Fin (m + 1) → K) from rfl,
            show w j = ((B j : C) : Fin (m + 1) ⊕ Fin (m + 1) → K) from rfl,
            Module.Basis.reindex_apply, Module.Basis.reindex_apply, hb]
          simp
      have hspan : Submodule.span K (Set.range w) = C := by
        have h := congrArg (Submodule.map C.subtype) B.span_eq
        rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at h
        rw [← h]
        congr 1
        rw [show Set.range w = C.subtype '' Set.range (⇑B) from Set.range_comp _ _]
      refine ⟨w, hw, ?_, hspan⟩
      intro y hy
      exact absurd hy (by simp)

private theorem fgt_exists_unit_vector (hσ : ∀ x, σ (σ x) = x) (hne : ∃ c, σ c ≠ c)
    (hN : ∀ a : K, σ a = a → a ≠ 0 → ∃ x : K, x * σ x = a)
    {D : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)} (hD : IsFlipflopSub σ D)
    (hDdim : Module.finrank K D = 1) :
    ∃ p ∈ D, quadPlus (m + 1) K p = 0 ∧ flipHerm σ p p = 1 := by
  have hDne : D ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hDdim
    omega
  obtain ⟨v, hvD, hvv⟩ := exists_anisotropic_of_isFlipflopSub hσ hne hD hDne
  have hv0 : v ≠ 0 := fun h => hvv (by rw [h, flipHerm_zero_right])
  have hfix : σ (flipHerm σ v v) = flipHerm σ v v := flipHerm_self_mem_fixed hσ v
  obtain ⟨a, ha⟩ := hN (flipHerm σ v v)⁻¹ (by rw [map_inv₀, hfix]) (inv_ne_zero hvv)
  refine ⟨a • v, D.smul_mem a hvD, ?_, ?_⟩
  · rw [QuadraticMap.map_smul]
    simp [hD.total v hvD]
  · rw [flipHerm_smul_left, flipHerm_smul_right]
    calc a * (σ a * flipHerm σ v v) = (a * σ a) * flipHerm σ v v := by ring
      _ = (flipHerm σ v v)⁻¹ * flipHerm σ v v := by rw [ha]
      _ = 1 := inv_mul_cancel₀ hvv

private theorem fgt_exists_hyperplane_flipflop (hσ : ∀ x, σ (σ x) = x)
    (hne : ∃ c, σ c ≠ c) {M T : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    (hM : IsSolid σ M) (hT : IsFlipflopSub σ T) (hTM : T ≤ M)
    (hTdim : Module.finrank K T + 2 ≤ m + 1) :
    ∃ C : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K),
      IsFlipflopSub σ C ∧ Module.finrank K C = m ∧ T ≤ C ∧ C ≤ M := by
  let D : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) := M ⊓ flipOrth σ T
  have hD : IsFlipflopSub σ D := fgt_isFlipflopSub_inf_flipOrth hσ hne hT hM.1 hTM
  have hDdim : Module.finrank K D = (m + 1) - Module.finrank K T := by
    rw [show D = M ⊓ flipOrth σ T from rfl,
      fgt_finrank_inf_flipOrth hσ hne hT hTM, hM.2]
  have hDne : D ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hDdim
    omega
  obtain ⟨v, hvD, hvv⟩ := exists_anisotropic_of_isFlipflopSub hσ hne hD hDne
  have hv0 : v ≠ 0 := fun h => hvv (by rw [h, flipHerm_zero_right])
  let p : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) := K ∙ v
  have hpM : p ≤ M :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hvD.1
  have hpOrthT : p ≤ flipOrth σ T :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hvD.2
  have hpt : IsFlipflopPt σ p :=
    (isFlipflopPt_span_singleton_iff hv0).mpr ⟨hD.total v hvD, hvv⟩
  refine ⟨M ⊓ flipOrth σ p, ?_, ?_, ?_, inf_le_left⟩
  · exact hM.1.inf_flipOrth_span hσ hvD.1 hvv
  · rw [fgt_finrank_inf_flipOrth hσ hne hpt.1 hpM, hM.2, hpt.2]
    omega
  · intro t ht
    refine ⟨hTM ht, ?_⟩
    change t ∈ flipOrth σ p
    rw [mem_flipOrth]
    intro w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [flipHerm_smul_left,
      (flipHerm_eq_zero_iff hσ).mp
        ((mem_flipOrth.mp (hpOrthT (Submodule.mem_span_singleton_self v))) t ht), mul_zero]

private theorem fgt_exists_chamber (E : QuadExt F K σ)
    {C M_even M_odd : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    (hC : IsFlipflopSub σ C) (hCdim : Module.finrank K C = m)
    (hMe : IsSolid σ M_even) (hCe : C ≤ M_even)
    (heven : Even ((m + 1) - Module.finrank K ↥(M_even ⊓ stdLag (m + 1) K)))
    (huniq : ∀ N : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K),
      (quadPlusForm (m + 1) K).IsLagrangian N → C ≤ N → N = M_even ∨ N = M_odd)
    (A : Finset (FlagVert σ m))
    (hAns : ∀ x ∈ A, Module.finrank K x.1 ≠ m + 1)
    (hAch : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → x.1 < y.1 ∨ y.1 < x.1)
    (hAle : ∀ x ∈ A, x.1 ≤ C) :
    ∃ c : DChamber σ (m + 1),
      (∀ x ∈ A, c.sub (Module.finrank K x.1) = x.1) ∧
        c.spanAt Finset.univ = M_even ∧ c.alt = M_odd := by
  have hσ : ∀ x, σ (σ x) = x := E.isUnitary.invol
  have hne : ∃ c, σ c ≠ c := E.isUnitary.exists_ne
  have hN : ∀ a : K, σ a = a → a ≠ 0 → ∃ x : K, x * σ x = a := by
    intro a ha ha0
    obtain ⟨x, hx⟩ := E.isUnitary.norm_surj a ha ha0
    exact ⟨x, by rw [mul_comm]; exact hx⟩
  obtain ⟨w, horth, hspanA, hspanC⟩ :=
    fgt_exists_adapted_basis hσ hne hN A m C hC hCdim hAns hAch hAle
  let D2 : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K) := M_even ⊓ flipOrth σ C
  have hD2 : IsFlipflopSub σ D2 := fgt_isFlipflopSub_inf_flipOrth hσ hne hC hMe.1 hCe
  have hD2dim : Module.finrank K D2 = 1 := by
    rw [show D2 = M_even ⊓ flipOrth σ C from rfl,
      fgt_finrank_inf_flipOrth hσ hne hC hCe, hMe.2, hCdim]
    omega
  obtain ⟨p, hpD, hpQ, hpNorm⟩ :=
    fgt_exists_unit_vector hσ hne hN hD2 hD2dim
  have hpM : p ∈ M_even := hpD.1
  have hpOrthC : p ∈ flipOrth σ C := hpD.2
  have hpne : p ≠ 0 := by
    intro h
    rw [h, flipHerm_zero_right] at hpNorm
    exact zero_ne_one hpNorm
  have hwC : ∀ i : Fin m, w i ∈ C := fun i => by
    rw [← hspanC]
    exact Submodule.subset_span ⟨i, rfl⟩
  let v : Fin (m + 1) → (Fin (m + 1) ⊕ Fin (m + 1) → K) :=
    Fin.snoc (α := fun _ => (Fin (m + 1) ⊕ Fin (m + 1) → K)) w p
  have hv_last : v (Fin.last m) = p := by
    change Fin.snoc (α := fun _ => (Fin (m + 1) ⊕ Fin (m + 1) → K)) w p (Fin.last m) = p
    exact Fin.snoc_last (α := fun _ => (Fin (m + 1) ⊕ Fin (m + 1) → K)) p w
  have hv_cast : ∀ i : Fin m, v i.castSucc = w i := fun i => by
    change Fin.snoc (α := fun _ => (Fin (m + 1) ⊕ Fin (m + 1) → K)) w p i.castSucc = w i
    exact Fin.snoc_castSucc (α := fun _ => (Fin (m + 1) ⊕ Fin (m + 1) → K)) p w i
  have hv : fgtOrthonormal σ v := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last => rw [hv_last]; exact hpQ
      | cast i => rw [hv_cast]; exact horth.1 i
    · intro i j
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => rw [hv_last]; exact fgt_polar_eq_zero_of_total (A := M_even) hMe.1.total hpM hpM
        | cast j =>
          rw [hv_last, hv_cast]
          exact fgt_polar_eq_zero_of_total (A := M_even) hMe.1.total hpM (hCe (hwC j))
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          rw [hv_cast, hv_last]
          exact fgt_polar_eq_zero_of_total (A := M_even) hMe.1.total (hCe (hwC i)) hpM
        | cast j => rw [hv_cast, hv_cast]; exact horth.2.1 i j
    · intro i j
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => rw [hv_last, if_pos rfl]; exact hpNorm
        | cast j =>
          rw [hv_last, hv_cast, if_neg (by
            intro h
            have := congrArg Fin.val h
            simp at this
            omega)]
          exact (flipHerm_eq_zero_iff hσ).mp ((mem_flipOrth.mp hpOrthC) (w j) (hwC j))
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          rw [hv_cast, hv_last, if_neg (by
            intro h
            have := congrArg Fin.val h
            simp at this
            omega)]
          exact (mem_flipOrth.mp hpOrthC) (w i) (hwC i)
        | cast j =>
          rw [hv_cast, hv_cast, horth.2.2]
          have hiff : (i.castSucc = j.castSucc) ↔ i = j :=
            ⟨fun h => Fin.castSucc_injective m h, fun h => by rw [h]⟩
          by_cases hij : i = j
          · rw [if_pos (hiff.mpr hij), if_pos hij]
          · rw [if_neg (fun h => hij (hiff.mp h)), if_neg hij]
  let f : FlipFrame σ (m + 1) :=
    FlipFrame.ofOrthonormal v hv.1 (fun i j _ => hv.2.1 i j) hv.2.2
  have hline : ∀ i : Fin m, f.line i.castSucc = K ∙ w i := fun i => by
    change K ∙ v i.castSucc = K ∙ w i
    rw [hv_cast]
  have hline_last : f.line (Fin.last m) = K ∙ p := by
    change K ∙ v (Fin.last m) = K ∙ p
    rw [hv_last]
  have hsub := fgt_sub_eq_fgtSpan f w hline
  have hspanm : fgtSpan w m = C := by
    simpa [fgtSpan] using hspanC
  have hsubm : f.sub m = C := by
    rw [hsub m le_rfl, hspanm]
  have hpC : p ∉ C := by
    intro hpCin
    have h0 : p ∈ C ⊓ flipOrth σ C := ⟨hpCin, hpOrthC⟩
    rw [inf_flipOrth_eq_bot hσ hC] at h0
    exact hpne (by simpa using h0)
  have hdisj : Disjoint C (K ∙ p) := by
    rw [Submodule.disjoint_def]
    intro x hxC hxp
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hxp
    by_cases ha : a = 0
    · rw [ha, zero_smul]
    · exfalso
      apply hpC
      have hp_eq : p = a⁻¹ • (a • p) := by
        rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
      rw [hp_eq]
      exact C.smul_mem a⁻¹ hxC
  have hsupdim : Module.finrank K ↥(C ⊔ K ∙ p) = m + 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq C (K ∙ p)
    rw [hdisj.eq_bot, finrank_bot, add_zero, hCdim, finrank_span_singleton hpne] at h
    omega
  have hsupM : C ⊔ K ∙ p = M_even := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · exact sup_le hCe ((Submodule.span_singleton_le_iff_mem _ _).mpr hpM)
    · rw [hsupdim, hMe.2]
  have hspanAt : f.spanAt Finset.univ = M_even := by
    rw [← FlipFrame.sub_of_le f (le_refl (m + 1)),
      FlipFrame.sub_succ f (by omega : m < m + 1), hsubm]
    have hlast : f.line (⟨m, by omega⟩ : Fin (m + 1)) = K ∙ p := by
      rw [show (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m from Fin.ext rfl, hline_last]
    rw [hlast, hsupM]
  let c : DChamber σ (m + 1) :=
    { toFlipFrame := f
      even_ruling := by
        rw [hspanAt]
        exact heven }
  have hsubc : ∀ d, d ≤ m → c.sub d = fgtSpan w d := fun d hd => hsub d hd
  refine ⟨c, ?_, hspanAt, ?_⟩
  · intro x hx
    have hdxm : Module.finrank K x.1 ≤ m := by
      have h1 : Module.finrank K x.1 ≠ m + 1 := hAns x hx
      have h2 : Module.finrank K x.1 ≠ m := x.2.2.2
      have h3 : Module.finrank K x.1 ≤ m + 1 := x.2.1.finrank_le
      omega
    rw [hsubc (Module.finrank K x.1) hdxm]
    exact hspanA x hx
  · have hCalt : C ≤ c.alt := by
      rw [FlipFrame.alt]
      rw [show c.sub m = C by rw [hsubc m le_rfl, hspanm]]
      exact le_sup_left
    have hAltSolid : IsSolid σ c.alt :=
      ⟨c.isFlipflopSub_alt hσ, c.finrank_alt hσ⟩
    have hAltOdd : ¬ Even ((m + 1) - Module.finrank K
        ↥(c.alt ⊓ stdLag (m + 1) K)) := not_even_ruling_alt hσ m c
    rcases huniq c.alt (IsSolid.isLagrangian hAltSolid) hCalt with h | h
    · exfalso
      rw [h] at hAltOdd
      exact hAltOdd heven
    · exact h


theorem exists_dChamber_of_isFlag (E : QuadExt F K σ) (hm : 2 ≤ m) {S : Set (FlagVert σ m)}
    (hS : IsFlag (flagGraph σ m) S) :
    ∃ c : DChamber σ (m + 1), ∀ x ∈ S, x.1 = c.elt (flagTyp x) := by
  classical
  have hσ : ∀ x, σ (σ x) = x := E.isUnitary.invol
  have hne : ∃ c, σ c ≠ c := E.isUnitary.exists_ne
  have hN : ∀ a : K, σ a = a → a ≠ 0 → ∃ x : K, x * σ x = a := by
    intro a ha ha0
    obtain ⟨x, hx⟩ := E.isUnitary.norm_surj a ha ha0
    exact ⟨x, by rw [mul_comm]; exact hx⟩
  let Sf : Finset (FlagVert σ m) := hS.1.toFinset
  let Ssol : Finset (FlagVert σ m) :=
    Sf.filter (fun x => Module.finrank K x.1 = m + 1)
  let Sns : Finset (FlagVert σ m) :=
    Sf.filter (fun x => ¬ Module.finrank K x.1 = m + 1)
  have hSfmem : ∀ {x : FlagVert σ m}, x ∈ Sf ↔ x ∈ S := fun {x} =>
    hS.1.mem_toFinset
  have hSsol_mem : ∀ {x : FlagVert σ m}, x ∈ Ssol ↔
      x ∈ S ∧ Module.finrank K x.1 = m + 1 := by
    intro x
    simp [Ssol, Sf, hSfmem]
  have hSns_mem : ∀ {x : FlagVert σ m}, x ∈ Sns ↔
      x ∈ S ∧ Module.finrank K x.1 ≠ m + 1 := by
    intro x
    simp [Sns, Sf, hSfmem]
  have hSns_chain : ∀ x ∈ Sns, ∀ y ∈ Sns, x ≠ y →
      x.1 < y.1 ∨ y.1 < x.1 := by
    intro x hx y hy hxy
    have hxS : x ∈ S := (hSns_mem.mp hx).1
    have hyS : y ∈ S := (hSns_mem.mp hy).1
    have hAdj : (flagGraph σ m).Adj x y := hS.2 hxS hyS hxy
    rcases hAdj with h | h | ⟨hxfin, -, -⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd hxfin (hSns_mem.mp hx).2
  have hSns_lt_solid : ∀ x ∈ Sns, ∀ y ∈ Ssol, x.1 < y.1 := by
    intro x hx y hy
    have hxS : x ∈ S := (hSns_mem.mp hx).1
    have hyS : y ∈ S := (hSsol_mem.mp hy).1
    have hxy : x ≠ y := by
      intro h
      subst h
      exact (hSns_mem.mp hx).2 (hSsol_mem.mp hy).2
    have hAdj : (flagGraph σ m).Adj x y := hS.2 hxS hyS hxy
    rcases hAdj with h | h | ⟨hxfin, -, -⟩
    · exact h
    · exfalso
      have hlt := Submodule.finrank_lt_finrank_of_lt h
      have hyfin := (hSsol_mem.mp hy).2
      have hxle := IsFlipflopSub.finrank_le x.2.1
      omega
    · exact absurd hxfin (hSns_mem.mp hx).2
  have hSsol_card_le_two : Ssol.card ≤ 2 := by
    let φ : FlagVert σ m → Fin 2 := fun x =>
      if flagTyp x = Fin.last m then 0 else 1
    have hsoltyp : ∀ x ∈ Ssol, flagTyp x = Fin.last m ∨
        flagTyp x = ⟨m - 1, by omega⟩ := by
      intro x hx
      rw [fgt_flagTyp_of_solid (hSsol_mem.mp hx).2]
      split_ifs with h
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hinj : ∀ x ∈ Ssol, ∀ y ∈ Ssol, φ x = φ y → x = y := by
      intro x hx y hy hxy
      by_contra hne
      have hxS : x ∈ S := (hSsol_mem.mp hx).1
      have hyS : y ∈ S := (hSsol_mem.mp hy).1
      have hAdj : (flagGraph σ m).Adj x y := hS.2 hxS hyS hne
      have htypne := flagTyp_ne_of_adj hσ (by omega : 1 ≤ m) hAdj
      apply htypne
      rcases hsoltyp x hx with hxlast | hxalt
      · rcases hsoltyp y hy with hylast | hyalt
        · rw [hxlast, hylast]
        · exfalso
          have hnotlast : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
            intro h
            have := congrArg Fin.val h
            simp at this
            omega
          have hφx : φ x = 0 := by simp [φ, hxlast]
          have hφy : φ y = 1 := by simp [φ, hyalt, hnotlast]
          have : (0 : Fin 2) = 1 := by rw [← hφx, ← hφy]; exact hxy
          exact zero_ne_one this
      · rcases hsoltyp y hy with hylast | hyalt
        · exfalso
          have hnotlast : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
            intro h
            have := congrArg Fin.val h
            simp at this
            omega
          have hφx : φ x = 1 := by simp [φ, hxalt, hnotlast]
          have hφy : φ y = 0 := by simp [φ, hylast]
          have : (1 : Fin 2) = 0 := by rw [← hφx, ← hφy]; exact hxy
          exact one_ne_zero this
        · rw [hxalt, hyalt]
    have h := Finset.card_le_card_of_injOn (s := Ssol) (t := Finset.univ) φ
      (fun x _ => Finset.mem_univ _) hinj
    simpa using h
  have finish : ∀ (C M_even M_odd : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K))
      (c : DChamber σ (m + 1)),
      (∀ y ∈ Ssol, C ≤ y.1) →
      (∀ N : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K),
        (quadPlusForm (m + 1) K).IsLagrangian N → C ≤ N →
          N = M_even ∨ N = M_odd) →
      Even ((m + 1) - Module.finrank K ↥(M_even ⊓ stdLag (m + 1) K)) →
      ¬ Even ((m + 1) - Module.finrank K ↥(M_odd ⊓ stdLag (m + 1) K)) →
      (∀ x ∈ Sns, c.sub (Module.finrank K x.1) = x.1) →
      c.spanAt Finset.univ = M_even → c.alt = M_odd →
      ∀ x ∈ S, x.1 = c.elt (flagTyp x) := by
    intro C M_even M_odd c hCsol huniq heven hodd hsub hspan hAlt x hxS
    have hxSf : x ∈ Sf := hSfmem.mpr hxS
    by_cases hxsolid : Module.finrank K x.1 = m + 1
    · have hxSsol : x ∈ Ssol := by
        exact Finset.mem_filter.mpr ⟨hxSf, hxsolid⟩
      have hxL : (quadPlusForm (m + 1) K).IsLagrangian x.1 :=
        IsSolid.isLagrangian ⟨x.2.1, hxsolid⟩
      have hxun := huniq x.1 hxL (hCsol x hxSsol)
      by_cases hxpar : Even ((m + 1) - Module.finrank K
          ↥(x.1 ⊓ stdLag (m + 1) K))
      · have hxMe : x.1 = M_even := by
          rcases hxun with h | h
          · exact h
          · exfalso
            rw [h] at hxpar
            exact hodd hxpar
        have htyp : flagTyp x = Fin.last m := by
          rw [fgt_flagTyp_of_solid hxsolid, if_pos hxpar]
        rw [hxMe, htyp, FlipFrame.elt, if_pos rfl,
          c.toFlipFrame.sub_of_le (le_refl (m + 1)), hspan]
      · have hxMo : x.1 = M_odd := by
          rcases hxun with h | h
          · exfalso
            rw [h] at hxpar
            exact hxpar heven
          · exact h
        have htyp : flagTyp x = ⟨m - 1, by omega⟩ := by
          rw [fgt_flagTyp_of_solid hxsolid, if_neg hxpar]
        have hnotlast : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
          intro h
          have := congrArg Fin.val h
          simp at this
          omega
        have hnear : ((⟨m - 1, by omega⟩ : Fin (m + 1)) : ℕ) + 1 = m := by
          simp
          omega
        rw [hxMo, htyp, FlipFrame.elt, if_neg hnotlast, if_pos hnear, hAlt]
    · have hxSns : x ∈ Sns := by
        exact Finset.mem_filter.mpr ⟨hxSf, hxsolid⟩
      have hxle := IsFlipflopSub.finrank_le x.2.1
      have hxnem := x.2.2.2
      have hxpos : 1 ≤ Module.finrank K x.1 :=
        Submodule.one_le_finrank_iff.mpr x.2.2.1
      have hxltm : Module.finrank K x.1 < m := by omega
      have htyp := fgt_flagTyp_of_not_solid hxsolid
      have hnotlast : flagTyp x ≠ Fin.last m := by
        rw [htyp]
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      have hnotalt : ((flagTyp x : Fin (m + 1)) : ℕ) + 1 ≠ m := by
        rw [htyp]
        simp
        omega
      have hlt : ((flagTyp x : Fin (m + 1)) : ℕ) + 1 < m := by
        rw [htyp]
        simp
        omega
      have hidx : ((flagTyp x : Fin (m + 1)) : ℕ) + 1 = Module.finrank K x.1 := by
        rw [htyp]
        simp
        omega
      rw [FlipFrame.elt, if_neg hnotlast, if_neg hnotalt, hidx]
      exact (hsub x hxSns).symm
  have hcard0 : Ssol.card = 0 ∨ Ssol.card = 1 ∨ Ssol.card = 2 := by
    omega
  rcases hcard0 with h0 | h1 | h2
  ·
    have hSsol_empty : Ssol = ∅ := Finset.card_eq_zero.mp h0
    by_cases hSns0 : Sns.Nonempty
    · obtain ⟨T, hTmem, hTmax⟩ :=
        Finset.exists_max_image Sns (fun x => Module.finrank K x.1) hSns0
      have hTns : Module.finrank K T.1 ≠ m + 1 := (hSns_mem.mp hTmem).2
      have hTle := IsFlipflopSub.finrank_le T.2.1
      have hTnem := T.2.2.2
      have hTdim : Module.finrank K T.1 + 2 ≤ m + 1 := by omega
      have hTlt : Module.finrank K T.1 < m + 1 := by omega
      obtain ⟨M, M', hMs, hM's, hTM, hTM', hev, hodd⟩ :=
        IsFlipflopSub.exists_solid_le E.isUnitary T.2.1 hTlt
      obtain ⟨C, hC, hCdim, hTC, hCM⟩ :=
        fgt_exists_hyperplane_flipflop hσ hne hMs T.2.1 hTM hTdim
      have hCdim1 : Module.finrank K C + 1 = m + 1 := by omega
      obtain ⟨M_even, M_odd, hMe, hMo, hCe, hCo, heven, hodd', huniq⟩ :=
        IsFlipflopSub.exists_two_solids hσ hC hCdim1
      have hML : (quadPlusForm (m + 1) K).IsLagrangian M := IsSolid.isLagrangian hMs
      have hMun := huniq M hML hCM
      have hMev : M = M_even := by
        rcases hMun with h | h
        · exact h
        · exfalso
          rw [h] at hev
          exact hodd' hev
      have hAle : ∀ x ∈ Sns, x.1 ≤ C := by
        intro x hx
        have hxT : x.1 ≤ T.1 := by
          by_cases hxT : x = T
          · rw [hxT]
          · have hAdj := hSns_chain x hx T hTmem hxT
            rcases hAdj with h | h
            · exact le_of_lt h
            · exfalso
              have hfin := Submodule.finrank_lt_finrank_of_lt h
              have hmax := hTmax x hx
              omega
        exact le_trans hxT hTC
      obtain ⟨c, hsub, hspan, hAlt⟩ :=
        fgt_exists_chamber E hC hCdim hMe hCe heven
          huniq Sns (fun x hx => (hSns_mem.mp hx).2) hSns_chain hAle
      refine ⟨c, finish C M_even M_odd c ?_ huniq heven hodd' hsub hspan hAlt⟩
      intro y hy
      rw [hSsol_empty] at hy
      exact absurd hy (by simp)
    · have hSns_empty : Sns = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSns0
      refine ⟨stdDChamber σ (m + 1), ?_⟩
      intro x hxS
      have hxSf : x ∈ Sf := hSfmem.mpr hxS
      by_cases hxsolid : Module.finrank K x.1 = m + 1
      · have hxSsol : x ∈ Ssol := Finset.mem_filter.mpr ⟨hxSf, hxsolid⟩
        rw [hSsol_empty] at hxSsol
        exact absurd hxSsol (by simp)
      · have hxSns : x ∈ Sns := Finset.mem_filter.mpr ⟨hxSf, hxsolid⟩
        rw [hSns_empty] at hxSns
        exact absurd hxSns (by simp)
  ·
    obtain ⟨M, hSsol_eq⟩ := Finset.card_eq_one.mp h1
    have hMmem : M ∈ Ssol := by rw [hSsol_eq]; simp
    have hMsolid : Module.finrank K M.1 = m + 1 := (hSsol_mem.mp hMmem).2
    have hMs : IsSolid σ M.1 := ⟨M.2.1, hMsolid⟩
    have hSsol_sub : ∀ y ∈ Ssol, y = M := by
      intro y hy
      rw [hSsol_eq] at hy
      simpa using hy
    by_cases hSns0 : Sns.Nonempty
    · obtain ⟨T, hTmem, hTmax⟩ :=
        Finset.exists_max_image Sns (fun x => Module.finrank K x.1) hSns0
      have hTns : Module.finrank K T.1 ≠ m + 1 := (hSns_mem.mp hTmem).2
      have hTle := IsFlipflopSub.finrank_le T.2.1
      have hTnem := T.2.2.2
      have hTdim : Module.finrank K T.1 + 2 ≤ m + 1 := by omega
      have hTM : T.1 ≤ M.1 := le_of_lt (hSns_lt_solid T hTmem M hMmem)
      obtain ⟨C, hC, hCdim, hTC, hCM⟩ :=
        fgt_exists_hyperplane_flipflop hσ hne hMs T.2.1 hTM hTdim
      have hCdim1 : Module.finrank K C + 1 = m + 1 := by omega
      obtain ⟨M_even, M_odd, hMe, hMo, hCe, hCo, heven, hodd, huniq⟩ :=
        IsFlipflopSub.exists_two_solids hσ hC hCdim1
      have hML : (quadPlusForm (m + 1) K).IsLagrangian M.1 := IsSolid.isLagrangian hMs
      have hMun := huniq M.1 hML hCM
      have hAle : ∀ x ∈ Sns, x.1 ≤ C := by
        intro x hx
        have hxT : x.1 ≤ T.1 := by
          by_cases hxT : x = T
          · rw [hxT]
          · have hAdj := hSns_chain x hx T hTmem hxT
            rcases hAdj with h | h
            · exact le_of_lt h
            · exfalso
              have hfin := Submodule.finrank_lt_finrank_of_lt h
              have hmax := hTmax x hx
              omega
        exact le_trans hxT hTC
      obtain ⟨c, hsub, hspan, hAlt⟩ :=
        fgt_exists_chamber E hC hCdim hMe hCe heven
          huniq Sns (fun x hx => (hSns_mem.mp hx).2) hSns_chain hAle
      refine ⟨c, finish C M_even M_odd c ?_ huniq heven hodd hsub hspan hAlt⟩
      intro y hy
      have hyM : y = M := hSsol_sub y hy
      rw [hyM]
      exact hCM
    ·
      have hSns_empty : Sns = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSns0
      have hbot : IsFlipflopSub σ (⊥ : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)) := by
        refine ⟨?_, ?_⟩
        · intro u hu
          have hu0 : u = 0 := by simpa using hu
          rw [hu0]
          simp
        · intro u hu _
          have hu0 : u = 0 := by simpa using hu
          exact hu0
      have hbotdim : Module.finrank K (⊥ : Submodule K
          (Fin (m + 1) ⊕ Fin (m + 1) → K)) + 2 ≤ m + 1 := by
        simp
        omega
      obtain ⟨C, hC, hCdim, hbotC, hCM⟩ :=
        fgt_exists_hyperplane_flipflop hσ hne hMs hbot (by simp) hbotdim
      have hCdim1 : Module.finrank K C + 1 = m + 1 := by omega
      obtain ⟨M_even, M_odd, hMe, hMo, hCe, hCo, heven, hodd, huniq⟩ :=
        IsFlipflopSub.exists_two_solids hσ hC hCdim1
      obtain ⟨c, hsub, hspan, hAlt⟩ :=
        fgt_exists_chamber E hC hCdim hMe hCe heven
          huniq Sns (fun x hx => (hSns_mem.mp hx).2) hSns_chain
          (fun x hx => by
            rw [hSns_empty] at hx
            exact absurd hx (by simp))
      refine ⟨c, finish C M_even M_odd c ?_ huniq heven hodd hsub hspan hAlt⟩
      intro y hy
      have hyM : y = M := hSsol_sub y hy
      rw [hyM]
      exact hCM
  ·
    obtain ⟨M₁, M₂, hM12, hSsol_eq⟩ := Finset.card_eq_two.mp h2
    have hM1mem : M₁ ∈ Ssol := by rw [hSsol_eq]; simp
    have hM2mem : M₂ ∈ Ssol := by rw [hSsol_eq]; simp
    have hM1solid : Module.finrank K M₁.1 = m + 1 := (hSsol_mem.mp hM1mem).2
    have hM2solid : Module.finrank K M₂.1 = m + 1 := (hSsol_mem.mp hM2mem).2
    have hM1S : M₁ ∈ S := (hSsol_mem.mp hM1mem).1
    have hM2S : M₂ ∈ S := (hSsol_mem.mp hM2mem).1
    have hM1Adj : (flagGraph σ m).Adj M₁ M₂ := hS.2 hM1S hM2S hM12
    have hCdim : Module.finrank K ↥(M₁.1 ⊓ M₂.1) = m := by
      rcases hM1Adj with hlt | hlt | ⟨-, -, hInf⟩
      · have := Submodule.finrank_lt_finrank_of_lt hlt
        omega
      · have := Submodule.finrank_lt_finrank_of_lt hlt
        omega
      · exact hInf
    have hM1L : (quadPlusForm (m + 1) K).IsLagrangian M₁.1 :=
      IsSolid.isLagrangian ⟨M₁.2.1, hM1solid⟩
    have hM2L : (quadPlusForm (m + 1) K).IsLagrangian M₂.1 :=
      IsSolid.isLagrangian ⟨M₂.2.1, hM2solid⟩
    have hC : IsFlipflopSub σ (M₁.1 ⊓ M₂.1) :=
      isFlipflopSub_inf_of_isLagrangian hσ M₁.2.1 hM1L M₂.2.1 hM2L (by omega)
    have hCdim1 : Module.finrank K ↥(M₁.1 ⊓ M₂.1) + 1 = m + 1 := by omega
    obtain ⟨M_even, M_odd, hMe, hMo, hCe, hCo, heven, hodd, huniq⟩ :=
      IsFlipflopSub.exists_two_solids hσ hC hCdim1
    have hAle : ∀ x ∈ Sns, x.1 ≤ M₁.1 ⊓ M₂.1 := by
      intro x hx
      exact le_inf (le_of_lt (hSns_lt_solid x hx M₁ hM1mem))
        (le_of_lt (hSns_lt_solid x hx M₂ hM2mem))
    obtain ⟨c, hsub, hspan, hAlt⟩ :=
      fgt_exists_chamber E hC hCdim hMe hCe heven
        huniq Sns (fun x hx => (hSns_mem.mp hx).2) hSns_chain hAle
    refine ⟨c, finish (M₁.1 ⊓ M₂.1) M_even M_odd c ?_ huniq heven hodd hsub hspan hAlt⟩
    intro y hy
    have hyM : y = M₁ ∨ y = M₂ := by
      rw [hSsol_eq] at hy
      simpa using hy
    rcases hyM with rfl | rfl
    · exact inf_le_left
    · exact inf_le_right


theorem flagTransitive_flagGraph [CharP K 2] (E : QuadExt F K σ) [Finite K] (hm : 3 ≤ m) :
    FlagTransitive ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) (flagGraph σ m)
      (flagChamber E m) := by
  intro S hS
  obtain ⟨c, hc⟩ := exists_dChamber_of_isFlag E (by omega) hS
  obtain ⟨g, hg⟩ := exists_smul_stdDChamber E (n := m + 1) (by omega) c
  refine ⟨g⁻¹, ?_⟩
  intro x hx
  refine ⟨flagTyp x, ?_⟩
  apply Subtype.ext
  rw [coe_flagChamber, coe_smul_flagVert, hc x hx,
    ← elt_smul E m g⁻¹ c (flagTyp x)]
  have hgc : g⁻¹ • c = stdDChamber σ (m + 1) := by
    rw [← hg]
    simp
  rw [hgc]

end CFSG.ClassicalInvolution.PhanDn
