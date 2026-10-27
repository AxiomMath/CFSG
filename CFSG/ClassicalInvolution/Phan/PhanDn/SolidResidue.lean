module

public import CFSG.ClassicalInvolution.Phan.PhanDn.Chambers
public import CFSG.ClassicalInvolution.Phan.PhanDn.FrameAdjacency
public import CFSG.ClassicalInvolution.Phan.PhanDn.Solid
public import CFSG.ClassicalInvolution.Phan.Frames
public import CFSG.ClassicalInvolution.Phan.PanelLift
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipFrame

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Unitary
open CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.PhanG

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

private theorem flipHerm_finset_sum_left {ι : Type*} (s : Finset ι)
    (f : ι → Fin n ⊕ Fin n → K) (v : Fin n ⊕ Fin n → K) :
    flipHerm σ (∑ i ∈ s, f i) v = ∑ i ∈ s, flipHerm σ (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, flipHerm_add_left, ih]

private theorem flipHerm_finset_sum_right {ι : Type*} (s : Finset ι)
    (f : ι → Fin n ⊕ Fin n → K) (v : Fin n ⊕ Fin n → K) :
    flipHerm σ v (∑ i ∈ s, f i) = ∑ i ∈ s, flipHerm σ v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, flipHerm_add_right, ih]

private theorem herm_single_right (j : Fin n) (x : Fin n → K) :
    herm σ x (Pi.single j (1 : K)) = σ (x j) := by
  rw [herm]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem IsSolid.exists_coord (hσ : IsUnitaryInvolution σ) {M : Submodule K (Fin n ⊕ Fin n → K)}
    (hM : IsSolid σ M) :
    ∃ φ : (Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K), Function.Injective φ ∧
      LinearMap.range φ = M ∧ ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormal_basis (n := n) hσ.invol hσ.exists_ne
    (fun a ha ha0 => by
      obtain ⟨c, hc⟩ := hσ.norm_surj a ha ha0
      exact ⟨c, by rwa [mul_comm] at hc⟩) hM.1
  let e : Fin (Module.finrank K M) ≃ Fin n := finCongr hM.2
  let v : Fin n → (Fin n ⊕ Fin n → K) := fun i => ((b (e.symm i) : M) : Fin n ⊕ Fin n → K)
  let φ : (Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) :=
    { toFun := fun x => ∑ i, x i • v i
      map_add' := by
        intro x y
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => add_smul (x i) (y i) (v i)
      map_smul' := by
        intro a x
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply] }
  have hφ : ∀ x, φ x = ∑ i, x i • v i := fun _ => rfl
  have hv_orth : ∀ i j, flipHerm σ (v i) (v j) = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simpa [v] using hb (e.symm i) (e.symm i)
    · have hne : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
      rw [if_neg hij]
      simpa [v, hne] using hb (e.symm i) (e.symm j)
  have hv_mem : ∀ i, v i ∈ M := fun i => (b (e.symm i)).2
  have hflip : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x := by
    intro x y
    rw [hφ, hφ]
    calc flipHerm σ (∑ i, x i • v i) (∑ j, y j • v j)
        = ∑ i, flipHerm σ (x i • v i) (∑ j, y j • v j) :=
          flipHerm_finset_sum_left _ _ _
      _ = ∑ i, ∑ j, flipHerm σ (x i • v i) (y j • v j) := by
          refine Finset.sum_congr rfl fun i _ => flipHerm_finset_sum_right _ _ _
      _ = ∑ i, ∑ j, (x i * σ (y j)) * (if i = j then 1 else 0) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [flipHerm_smul_left, flipHerm_smul_right, hv_orth]
          ring
      _ = ∑ i, x i * σ (y i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji
            rw [if_neg (Ne.symm hji), mul_zero]
          · intro h
            exact absurd (Finset.mem_univ i) h
      _ = ∑ i, σ (y i) * x i :=
          Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = herm σ y x := rfl
  have hinj : Function.Injective φ := by
    intro x y hxy
    funext j
    have h1 := hflip (Pi.single j (1 : K)) x
    rw [hxy] at h1
    rw [hflip (Pi.single j (1 : K)) y, herm_single_right, herm_single_right] at h1
    exact (σ.injective h1).symm
  have hrange : LinearMap.range φ = M := by
    have hle : LinearMap.range φ ≤ M := by
      rintro _ ⟨x, rfl⟩
      rw [hφ]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hv_mem i)
    have hdim : Module.finrank K ↥(LinearMap.range φ) = Module.finrank K M := by
      rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card,
        Fintype.card_fin, hM.2]
    refine le_antisymm hle ?_
    rw [← Submodule.eq_of_le_of_finrank_eq hle hdim]
  exact ⟨φ, hinj, hrange, hflip⟩

theorem nondeg_iff_isFlipflopSub_map {M : Submodule K (Fin n ⊕ Fin n → K)}
    {φ : (Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)}
    (hσ : ∀ x, σ (σ x) = x) (hM : IsSolid σ M) (hinj : Function.Injective φ)
    (hrange : LinearMap.range φ = M) (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x)
    {W : Submodule K (Fin n → K)} :
    Nondeg σ W ↔ IsFlipflopSub σ (W.map φ) := by
  constructor
  · intro hW
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact hM.1.total (φ x) (hrange ▸ LinearMap.mem_range_self φ x)
    · rintro _ ⟨x, hx, rfl⟩ hper
      have hx0 : x = 0 := by
        refine hW x hx fun t ht => ?_
        have h1 : flipHerm σ (φ x) (φ t) = 0 := hper (φ t) (Submodule.mem_map_of_mem ht)
        rw [hφ] at h1
        exact herm_eq_zero_comm (σ := σ) hσ h1
      rw [hx0, map_zero]
  · intro hU x hx hper
    have hzero : φ x = 0 := by
      refine hU.nondeg (φ x) (Submodule.mem_map_of_mem hx) fun v hv => ?_
      obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.mp hv
      rw [hφ]
      exact herm_eq_zero_comm (σ := σ) hσ (hper t ht)
    exact hinj (by rw [hzero, map_zero])

theorem isCollinear_iff_flipColl {M : Submodule K (Fin n ⊕ Fin n → K)}
    {φ : (Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)}
    (hσ : ∀ x, σ (σ x) = x) (hM : IsSolid σ M) (hinj : Function.Injective φ)
    (hrange : LinearMap.range φ = M) (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x)
    {x y : Submodule K (Fin n → K)} :
    IsCollinear σ x y ↔ FlipColl σ (x.map φ) (y.map φ) := by
  constructor
  · rintro ⟨hxy, hne⟩
    refine ⟨?_, ?_⟩
    · intro hmap
      exact hxy (Submodule.map_injective_of_injective hinj hmap)
    · exact (Submodule.map_sup x y φ) ▸
        (nondeg_iff_isFlipflopSub_map hσ hM hinj hrange hφ (W := x ⊔ y)).mp hne
  · rintro ⟨hxy, hU⟩
    refine ⟨fun h => hxy (by rw [h]), (nondeg_iff_isFlipflopSub_map hσ hM hinj hrange hφ
      (W := x ⊔ y)).mpr ?_⟩
    exact (Submodule.map_sup x y φ).symm ▸ hU

@[expose] def solidTypeB (t : ℕ) (j : Fin (t + 2)) : Fin (t + 3) :=
  if (j : ℕ) + 1 = t + 2 then Fin.last _ else j.castSucc

theorem solidTypeB_injective (t : ℕ) : Function.Injective (solidTypeB t) := by
  intro i j hij
  unfold solidTypeB at hij
  by_cases hi : (i : ℕ) + 1 = t + 2
  · rw [if_pos hi] at hij
    have hj : (j : ℕ) + 1 = t + 2 := by
      by_contra h
      rw [if_neg h] at hij
      have hval := congrArg Fin.val hij
      simp only [Fin.val_last, Fin.val_castSucc] at hval
      omega
    apply Fin.ext
    omega
  · rw [if_neg hi] at hij
    have hj : ¬ (j : ℕ) + 1 = t + 2 := by
      intro h
      rw [if_pos h] at hij
      have hval := congrArg Fin.val hij
      simp only [Fin.val_last, Fin.val_castSucc] at hval
      omega
    rw [if_neg hj] at hij
    exact Fin.ext (by simpa using congrArg Fin.val hij)

theorem solidTypeB_zero (t : ℕ) : solidTypeB t 0 = 0 := by
  unfold solidTypeB
  rw [if_neg (by rw [Fin.val_zero]; omega)]
  rfl

structure SolidChart (σ : K ≃+* K) (t : ℕ)
    (M : Submodule K (Fin (t + 3) ⊕ Fin (t + 3) → K)) where
  φ : (Fin (t + 3) → K) →ₗ[K] (Fin (t + 3) ⊕ Fin (t + 3) → K)
  injective_φ : Function.Injective φ
  range_φ : LinearMap.range φ = M
  flipHerm_φ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x
  τ : Fin (t + 2) → Fin (t + 3)
  injective_τ : Function.Injective τ
  τ_zero : τ 0 = 0
  emb : Frame σ (t + 3) → DChamber σ (t + 3)
  emb_line_zero : ∀ c, (emb c).line 0 = (c.line 0).map φ

section Chart

variable {t : ℕ} {M : Submodule K (Fin (t + 3) ⊕ Fin (t + 3) → K)}
  {φ : (Fin (t + 3) → K) →ₗ[K] (Fin (t + 3) ⊕ Fin (t + 3) → K)}

private theorem quadPlus_phi_eq_zero (hM : IsSolid σ M) (hrange : LinearMap.range φ = M)
    (x : Fin (t + 3) → K) : quadPlus (t + 3) K (φ x) = 0 :=
  hM.1.total (φ x) (hrange ▸ LinearMap.mem_range_self φ x)

private theorem polar_phi_phi_eq_zero (hM : IsSolid σ M) (hrange : LinearMap.range φ = M)
    (x y : Fin (t + 3) → K) :
    polar (quadPlus (t + 3) K) (φ x) (φ y) = 0 := by
  have hxM : φ x ∈ M := hrange ▸ LinearMap.mem_range_self φ x
  have hyM : φ y ∈ M := hrange ▸ LinearMap.mem_range_self φ y
  have h := QuadraticMap.map_add (quadPlus (t + 3) K) (φ x) (φ y)
  rw [hM.1.total (φ x) hxM, hM.1.total (φ y) hyM,
    hM.1.total (φ x + φ y) (M.add_mem hxM hyM)] at h
  simpa using h.symm

private theorem isFlipflopPt_map_line (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x)
    (c : Frame σ (t + 3)) (j : Fin (t + 3)) :
    IsFlipflopPt σ ((c.line j).map φ) := by
  obtain ⟨v, hv, horth⟩ := c.exists_gen hσ
  have hvj : v j ≠ 0 := by
    intro h0
    have h := horth j j
    rw [h0, herm_zero_left, if_pos rfl] at h
    exact one_ne_zero h.symm
  have hw0 : φ (v j) ≠ 0 := fun h => hvj (hinj (by rw [h, map_zero]))
  have hline : (c.line j).map φ = K ∙ φ (v j) := by
    rw [hv j, Submodule.map_span, Set.image_singleton]
  rw [hline, isFlipflopPt_span_singleton_iff hw0]
  exact ⟨quadPlus_phi_eq_zero hM hrange (v j), by rw [hφ, horth j j]; simp⟩

private theorem isFlipflopPt_dFlipSub (hσ : ∀ x, σ (σ x) = x)
    {p : Submodule K (Fin (t + 3) ⊕ Fin (t + 3) → K)} (hp : IsFlipflopPt σ p) :
    IsFlipflopPt σ (dFlipSub σ p) := by
  obtain ⟨v, rfl, hq, hh⟩ := hp.exists_eq_span
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, flipHerm_zero_right] at hh
    exact hh rfl
  have hw0 : dFlip σ v ≠ 0 := by
    intro h
    apply hv0
    have h' := congrArg (dFlip σ) h
    rw [dFlip_dFlip hσ] at h'
    have hz : dFlip σ (0 : Fin (t + 3) ⊕ Fin (t + 3) → K) = 0 := by
      funext x
      cases x <;> simp [dFlip]
    rw [hz] at h'
    exact h'
  rw [dFlipSub_span_singleton, isFlipflopPt_span_singleton_iff hw0]
  exact ⟨by rw [quadPlus_dFlip, hq, map_zero],
    by rw [flipHerm_dFlip_dFlip hσ]; exact fun h => hh ((map_eq_zero_iff σ σ.injective).mp h)⟩

private theorem isFlipflopPt_dFlipSub_map_line (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x)
    (c : Frame σ (t + 3)) (j : Fin (t + 3)) :
    IsFlipflopPt σ (dFlipSub σ ((c.line j).map φ)) :=
  isFlipflopPt_dFlipSub hσ.invol (isFlipflopPt_map_line hσ hM hinj hrange hφ c j)

private theorem spanAt_eq_map_of_line_eq_on {m : ℕ} {d : FlipFrame σ m}
    (c : Frame σ m) (φ : (Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)) (S : Finset (Fin m))
    (hS : ∀ l ∈ S, d.line l = (c.line l).map φ) :
    d.spanAt S = (c.spanAt S).map φ := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [FlipFrame.spanAt_empty, Frame.spanAt_empty, Submodule.map_bot]
  | insert a S ha ih =>
    rw [FlipFrame.spanAt_insert, Frame.spanAt_insert, Submodule.map_sup,
      hS a (Finset.mem_insert_self a S),
      ih fun l hl => hS l (Finset.mem_insert_of_mem hl)]

private theorem map_sup_map {m : ℕ} (ψ : (Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K))
    (a b : Submodule K (Fin m → K)) : a.map ψ ⊔ b.map ψ = (a ⊔ b).map ψ :=
  (Submodule.map_sup a b ψ).symm

private theorem comap_map_eq_of_le {L : Submodule K (Fin (t + 3) ⊕ Fin (t + 3) → K)}
    (hrange : LinearMap.range φ = M) (hL : L ≤ M) :
    (Submodule.comap φ L).map φ = L := by
  rw [Submodule.map_comap_eq, hrange, inf_eq_right.mpr hL]

private theorem finrank_comap_eq_of_le (hinj : Function.Injective φ)
    (hrange : LinearMap.range φ = M) {L : Submodule K (Fin (t + 3) ⊕ Fin (t + 3) → K)}
    (hL : L ≤ M) :
    Module.finrank K ↥(Submodule.comap φ L) = Module.finrank K ↥L :=
  (Submodule.comap_equiv_self_of_inj_of_le hinj (hrange.symm ▸ hL)).finrank_eq

private noncomputable def comapFrame (hσ : ∀ x, σ (σ x) = x)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x)
    {L : Fin (t + 3) → Submodule K (Fin (t + 3) ⊕ Fin (t + 3) → K)}
    (hL : ∀ j, L j ≤ M) (hpt : ∀ j, IsFlipflopPt σ (L j))
    (horth : ∀ i j, i ≠ j → ∀ u ∈ L i, ∀ v ∈ L j, flipHerm σ u v = 0) :
    Frame σ (t + 3) where
  line j := Submodule.comap φ (L j)
  finrank_line j := by
    rw [finrank_comap_eq_of_le hinj hrange (hL j)]
    exact (hpt j).2
  nondeg_line j := by
    intro s hs hper
    have hs' : φ s ∈ L j := comap_map_eq_of_le hrange (hL j) ▸ Submodule.mem_map_of_mem hs
    have h0 : φ s = 0 := by
      refine (hpt j).1.nondeg (φ s) hs' fun v hv => ?_
      obtain ⟨u, hu, rfl⟩ :=
        Submodule.mem_map.mp ((comap_map_eq_of_le hrange (hL j)).symm ▸ hv)
      rw [hφ]
      exact herm_eq_zero_comm (σ := σ) hσ (hper u hu)
    exact hinj (by rw [h0, map_zero])
  orth_line i j hij u hu v hv := by
    have hui : φ u ∈ L i := comap_map_eq_of_le hrange (hL i) ▸ Submodule.mem_map_of_mem hu
    have hvj : φ v ∈ L j := comap_map_eq_of_le hrange (hL j) ▸ Submodule.mem_map_of_mem hv
    have h1 : flipHerm σ (φ u) (φ v) = 0 := horth i j hij (φ u) hui (φ v) hvj
    rw [hφ] at h1
    exact herm_eq_zero_comm (σ := σ) hσ h1

private noncomputable def evenFrame (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x) (c : Frame σ (t + 3)) :
    FlipFrame σ (t + 3) where
  line j := (c.line j).map φ
  isFlipflopPt_line j := isFlipflopPt_map_line hσ hM hinj hrange hφ c j
  polar_eq_zero _ _ _ u hu v hv := by
    obtain ⟨u₀, -, rfl⟩ := Submodule.mem_map.mp hu
    obtain ⟨v₀, -, rfl⟩ := Submodule.mem_map.mp hv
    exact polar_phi_phi_eq_zero hM hrange u₀ v₀
  flipHerm_eq_zero i j hij u hu v hv := by
    obtain ⟨u₀, hu₀, rfl⟩ := Submodule.mem_map.mp hu
    obtain ⟨v₀, hv₀, rfl⟩ := Submodule.mem_map.mp hv
    rw [hφ]
    exact herm_eq_zero_comm (σ := σ) hσ.invol (c.orth_line i j hij u₀ hu₀ v₀ hv₀)

private theorem evenFrame_spanAt_univ (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x) (c : Frame σ (t + 3)) :
    (evenFrame hσ hM hinj hrange hφ c).spanAt Finset.univ = M := by
  rw [spanAt_eq_map_of_line_eq_on (d := evenFrame hσ hM hinj hrange hφ c) c φ Finset.univ
    (fun l _ => rfl), Frame.spanAt_univ hσ, Submodule.map_top]
  exact hrange

private noncomputable def evenEmb (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x)
    (hEven : Even ((t + 3) - Module.finrank K ↥(M ⊓ stdLag (t + 3) K)))
    (c : Frame σ (t + 3)) : DChamber σ (t + 3) where
  toFlipFrame := evenFrame hσ hM hinj hrange hφ c
  even_ruling := by
    rw [evenFrame_spanAt_univ hσ hM hinj hrange hφ c]
    exact hEven

private theorem evenEmb_line (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x)
    (hEven : Even ((t + 3) - Module.finrank K ↥(M ⊓ stdLag (t + 3) K)))
    (c : Frame σ (t + 3)) (j : Fin (t + 3)) :
    (evenEmb hσ hM hinj hrange hφ hEven c).line j = (c.line j).map φ :=
  rfl

private theorem evenEmb_spanAt_univ (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x)
    (hEven : Even ((t + 3) - Module.finrank K ↥(M ⊓ stdLag (t + 3) K)))
    (c : Frame σ (t + 3)) :
    (evenEmb hσ hM hinj hrange hφ hEven c).spanAt Finset.univ = M :=
  evenFrame_spanAt_univ hσ hM hinj hrange hφ c

private theorem evenEmb_isTypeMorphism (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x)
    (hEven : Even ((t + 3) - Module.finrank K ↥(M ⊓ stdLag (t + 3) K))) :
    IsTypeMorphism (frameSystem σ (t + 2)) (dChamberSystem σ (t + 2))
      (fun i => i.castSucc) (evenEmb hσ hM hinj hrange hφ hEven) := by
  intro i x y hxy
  rw [dChamberSystem_adj_iff]
  refine (FlipFrame.elt_eq_elt_iff_castSucc hσ.invol (k := i)
    (c := (evenEmb hσ hM hinj hrange hφ hEven x).toFlipFrame)
    (d := (evenEmb hσ hM hinj hrange hφ hEven y).toFlipFrame)).mpr ⟨?_, ?_⟩
  · intro j hj1 hj2
    rw [evenEmb_line, evenEmb_line, hxy j hj1 hj2]
  · rw [evenEmb_line, evenEmb_line, evenEmb_line, evenEmb_line, map_sup_map, map_sup_map,
      adj_sup_eq hσ hxy]

private theorem evenEmb_isPanelLift (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x)
    (hEven : Even ((t + 3) - Module.finrank K ↥(M ⊓ stdLag (t + 3) K))) :
    IsPanelLift (frameSystem σ (t + 2)) (dChamberSystem σ (t + 2))
      (fun i => i.castSucc) (evenEmb hσ hM hinj hrange hφ hEven) := by
  intro i x d hadj
  rw [dChamberSystem_adj_iff] at hadj
  have hlast : (i.castSucc : Fin (t + 3)) ≠ Fin.last (t + 2) := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_last] at hval
    omega
  have hspan : d.spanAt Finset.univ = M := by
    have h := hadj (Fin.last (t + 2)) hlast.symm
    rw [FlipFrame.elt_last, FlipFrame.elt_last,
      FlipFrame.sub_of_le (c := (evenEmb hσ hM hinj hrange hφ hEven x).toFlipFrame)
        (j := t + 3) le_rfl,
      FlipFrame.sub_of_le (c := d.toFlipFrame) (j := t + 3) le_rfl,
      evenEmb_spanAt_univ hσ hM hinj hrange hφ hEven x] at h
    exact h.symm
  have hle : ∀ j, d.line j ≤ M := by
    intro j
    rw [← hspan]
    exact d.line_le_spanAt (Finset.mem_univ j)
  let y := comapFrame hσ.invol hinj hrange hφ hle d.isFlipflopPt_line
    fun i j hij u hu v hv => d.flipHerm_eq_zero i j hij u hu v hv
  have hyline : ∀ j, (y.line j).map φ = d.line j := fun j =>
    comap_map_eq_of_le hrange (hle j)
  have hlines := (FlipFrame.elt_eq_elt_iff_castSucc hσ.invol (k := i)
    (c := (evenEmb hσ hM hinj hrange hφ hEven x).toFlipFrame)
    (d := d.toFlipFrame)).mp hadj
  have hyadj : (frameSystem σ (t + 2)).adj i x y := by
    intro j hj1 hj2
    refine Submodule.map_injective_of_injective hinj ?_
    rw [show (x.line j).map φ = (evenEmb hσ hM hinj hrange hφ hEven x).line j from
      (evenEmb_line hσ hM hinj hrange hφ hEven x j).symm, hlines.1 j hj1 hj2, hyline j]
  have hemb : evenEmb hσ hM hinj hrange hφ hEven y = d := by
    apply DChamber.ext
    funext j
    rw [evenEmb_line, hyline j]
  exact ⟨y, hyadj, hemb⟩

private noncomputable def oddLine (φ : (Fin (t + 3) → K) →ₗ[K] (Fin (t + 3) ⊕ Fin (t + 3) → K))
    (c : Frame σ (t + 3)) (j : Fin (t + 3)) :
    Submodule K (Fin (t + 3) ⊕ Fin (t + 3) → K) :=
  if j = Fin.last (t + 2) then dFlipSub σ ((c.line j).map φ) else (c.line j).map φ

private theorem oddLine_last (φ : (Fin (t + 3) → K) →ₗ[K] (Fin (t + 3) ⊕ Fin (t + 3) → K))
    (c : Frame σ (t + 3)) :
    oddLine φ c (Fin.last (t + 2)) =
      dFlipSub σ ((c.line (Fin.last (t + 2))).map φ) := by
  rw [oddLine, if_pos rfl]

private theorem oddLine_of_ne (φ : (Fin (t + 3) → K) →ₗ[K] (Fin (t + 3) ⊕ Fin (t + 3) → K))
    (c : Frame σ (t + 3)) {j : Fin (t + 3)} (hj : j ≠ Fin.last (t + 2)) :
    oddLine φ c j = (c.line j).map φ := by
  rw [oddLine, if_neg hj]

private noncomputable def oddFrame (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x) (c : Frame σ (t + 3)) :
    FlipFrame σ (t + 3) where
  line := oddLine φ c
  isFlipflopPt_line j := by
    by_cases hj : j = Fin.last (t + 2)
    · rw [oddLine, if_pos hj]
      exact isFlipflopPt_dFlipSub_map_line hσ hM hinj hrange hφ c j
    · rw [oddLine, if_neg hj]
      exact isFlipflopPt_map_line hσ hM hinj hrange hφ c j
  polar_eq_zero i j hij u hu v hv := by
    change u ∈ oddLine φ c i at hu
    change v ∈ oddLine φ c j at hv
    by_cases hi : i = Fin.last (t + 2)
    · subst hi
      have hj : j ≠ Fin.last (t + 2) := Ne.symm hij
      rw [oddLine, if_pos rfl] at hu
      rw [oddLine, if_neg hj] at hv
      obtain ⟨w₀, hw₀, hw⟩ := Submodule.mem_map.mp ((mem_dFlipSub hσ.invol).mp hu)
      obtain ⟨v₀, hv₀, rfl⟩ := Submodule.mem_map.mp hv
      have hu_eq : u = dFlip σ (φ w₀) := by rw [hw, dFlip_dFlip hσ.invol]
      rw [hu_eq, polar_comm, ← flipHerm, hφ]
      exact herm_eq_zero_comm (σ := σ) hσ.invol
        (c.orth_line j (Fin.last (t + 2)) hj v₀ hv₀ w₀ hw₀)
    · by_cases hj : j = Fin.last (t + 2)
      · subst hj
        rw [oddLine, if_neg hi] at hu
        rw [oddLine, if_pos rfl] at hv
        obtain ⟨u₀, hu₀, rfl⟩ := Submodule.mem_map.mp hu
        obtain ⟨w₀, hw₀, hw⟩ := Submodule.mem_map.mp ((mem_dFlipSub hσ.invol).mp hv)
        have hv_eq : v = dFlip σ (φ w₀) := by rw [hw, dFlip_dFlip hσ.invol]
        rw [hv_eq, ← flipHerm, hφ]
        exact herm_eq_zero_comm (σ := σ) hσ.invol
          (c.orth_line i (Fin.last (t + 2)) hi u₀ hu₀ w₀ hw₀)
      · rw [oddLine, if_neg hi] at hu
        rw [oddLine, if_neg hj] at hv
        obtain ⟨u₀, hu₀, rfl⟩ := Submodule.mem_map.mp hu
        obtain ⟨v₀, hv₀, rfl⟩ := Submodule.mem_map.mp hv
        exact polar_phi_phi_eq_zero hM hrange u₀ v₀
  flipHerm_eq_zero i j hij u hu v hv := by
    change u ∈ oddLine φ c i at hu
    change v ∈ oddLine φ c j at hv
    by_cases hi : i = Fin.last (t + 2)
    · subst hi
      have hj : j ≠ Fin.last (t + 2) := Ne.symm hij
      rw [oddLine, if_pos rfl] at hu
      rw [oddLine, if_neg hj] at hv
      obtain ⟨w₀, hw₀, hw⟩ := Submodule.mem_map.mp ((mem_dFlipSub hσ.invol).mp hu)
      obtain ⟨v₀, hv₀, rfl⟩ := Submodule.mem_map.mp hv
      have hu_eq : u = dFlip σ (φ w₀) := by rw [hw, dFlip_dFlip hσ.invol]
      rw [hu_eq, flipHerm, polar_dFlip, polar_phi_phi_eq_zero hM hrange w₀ v₀, map_zero]
    · by_cases hj : j = Fin.last (t + 2)
      · subst hj
        rw [oddLine, if_neg hi] at hu
        rw [oddLine, if_pos rfl] at hv
        obtain ⟨u₀, hu₀, rfl⟩ := Submodule.mem_map.mp hu
        obtain ⟨w₀, hw₀, hw⟩ := Submodule.mem_map.mp ((mem_dFlipSub hσ.invol).mp hv)
        have hv_eq : v = dFlip σ (φ w₀) := by rw [hw, dFlip_dFlip hσ.invol]
        rw [hv_eq, flipHerm, dFlip_dFlip hσ.invol, polar_phi_phi_eq_zero hM hrange u₀ w₀]
      · rw [oddLine, if_neg hi] at hu
        rw [oddLine, if_neg hj] at hv
        obtain ⟨u₀, hu₀, rfl⟩ := Submodule.mem_map.mp hu
        obtain ⟨v₀, hv₀, rfl⟩ := Submodule.mem_map.mp hv
        rw [hφ]
        exact herm_eq_zero_comm (σ := σ) hσ.invol (c.orth_line i j hij u₀ hu₀ v₀ hv₀)

private theorem oddFrame_line_last (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x) (c : Frame σ (t + 3)) :
    (oddFrame hσ hM hinj hrange hφ c).line (Fin.last (t + 2)) =
      dFlipSub σ ((c.line (Fin.last (t + 2))).map φ) := by
  change oddLine φ c (Fin.last (t + 2)) = _
  rw [oddLine_last]

private theorem oddFrame_line_of_ne (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x) (c : Frame σ (t + 3))
    {j : Fin (t + 3)} (hj : j ≠ Fin.last (t + 2)) :
    (oddFrame hσ hM hinj hrange hφ c).line j = (c.line j).map φ := by
  change oddLine φ c j = _
  rw [oddLine_of_ne φ c hj]

private theorem oddFrame_sub (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x) (c : Frame σ (t + 3))
    {j : ℕ} (hj : j ≤ t + 2) :
    (oddFrame hσ hM hinj hrange hφ c).sub j =
      (c.spanAt (Finset.univ.filter fun l : Fin (t + 3) => (l : ℕ) < j)).map φ := by
  rw [FlipFrame.sub]
  refine spanAt_eq_map_of_line_eq_on (d := oddFrame hσ hM hinj hrange hφ c) c φ _ fun l hl => ?_
  rw [Finset.mem_filter] at hl
  have hl' : l ≠ Fin.last (t + 2) := by
    intro h
    rw [h] at hl
    simp only [Fin.val_last] at hl
    omega
  exact oddFrame_line_of_ne hσ hM hinj hrange hφ c hl'

private theorem oddFrame_alt (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x) (c : Frame σ (t + 3)) :
    (oddFrame hσ hM hinj hrange hφ c).alt = M := by
  rw [FlipFrame.alt, oddFrame_sub hσ hM hinj hrange hφ c (le_refl _), oddFrame_line_last,
    dFlipSub_dFlipSub hσ.invol]
  have hins : insert (Fin.last (t + 2))
      (Finset.univ.filter fun l : Fin (t + 3) => (l : ℕ) < t + 2) = Finset.univ := by
    ext l
    rw [Finset.mem_insert, Finset.mem_filter]
    constructor
    · rintro (rfl | ⟨-, h⟩) <;> exact Finset.mem_univ _
    · intro _
      by_cases h : (l : ℕ) < t + 2
      · exact Or.inr ⟨Finset.mem_univ _, h⟩
      · left
        exact Fin.ext (by simp only [Fin.val_last]; omega)
  have hsp : c.spanAt (Finset.univ.filter fun l : Fin (t + 3) => (l : ℕ) < t + 2) ⊔
      c.line (Fin.last (t + 2)) = ⊤ := by
    have h := Frame.spanAt_insert c (Fin.last (t + 2))
      (Finset.univ.filter fun l : Fin (t + 3) => (l : ℕ) < t + 2)
    rw [hins, Frame.spanAt_univ hσ] at h
    rw [sup_comm]
    exact h.symm
  have hmap := congrArg (fun W => W.map φ) hsp
  rw [Submodule.map_sup, Submodule.map_top, hrange] at hmap
  exact hmap

private noncomputable def oddEmb (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x)
    (hOdd : ¬ Even ((t + 3) - Module.finrank K ↥(M ⊓ stdLag (t + 3) K)))
    (c : Frame σ (t + 3)) : DChamber σ (t + 3) where
  toFlipFrame := oddFrame hσ hM hinj hrange hφ c
  even_ruling := by
    have hiff := FlipFrame.even_iff_not_even_alt (m := t + 2) hσ.invol
      (oddFrame hσ hM hinj hrange hφ c)
    rw [oddFrame_alt hσ hM hinj hrange hφ c] at hiff
    exact hiff.mpr hOdd

private theorem oddEmb_line_last (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x)
    (hOdd : ¬ Even ((t + 3) - Module.finrank K ↥(M ⊓ stdLag (t + 3) K)))
    (c : Frame σ (t + 3)) :
    (oddEmb hσ hM hinj hrange hφ hOdd c).line (Fin.last (t + 2)) =
      dFlipSub σ ((c.line (Fin.last (t + 2))).map φ) :=
  oddFrame_line_last hσ hM hinj hrange hφ c

private theorem oddEmb_line_of_ne (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x)
    (hOdd : ¬ Even ((t + 3) - Module.finrank K ↥(M ⊓ stdLag (t + 3) K)))
    (c : Frame σ (t + 3)) {j : Fin (t + 3)} (hj : j ≠ Fin.last (t + 2)) :
    (oddEmb hσ hM hinj hrange hφ hOdd c).line j = (c.line j).map φ :=
  oddFrame_line_of_ne hσ hM hinj hrange hφ c hj

private theorem oddEmb_alt (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x)
    (hOdd : ¬ Even ((t + 3) - Module.finrank K ↥(M ⊓ stdLag (t + 3) K)))
    (c : Frame σ (t + 3)) :
    (oddEmb hσ hM hinj hrange hφ hOdd c).alt = M :=
  oddFrame_alt hσ hM hinj hrange hφ c

private theorem oddEmb_isTypeMorphism (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x)
    (hOdd : ¬ Even ((t + 3) - Module.finrank K ↥(M ⊓ stdLag (t + 3) K))) :
    IsTypeMorphism (frameSystem σ (t + 2)) (dChamberSystem σ (t + 2))
      (solidTypeB t) (oddEmb hσ hM hinj hrange hφ hOdd) := by
  intro i x y hxy
  rw [dChamberSystem_adj_iff]
  have hib := i.is_lt
  by_cases hi : (i : ℕ) + 1 = t + 2
  · have hτ : solidTypeB t i = Fin.last (t + 2) := by
      unfold solidTypeB
      rw [if_pos hi]
    rw [hτ]
    have hcast : i.castSucc = (⟨t + 1, by omega⟩ : Fin (t + 3)) :=
      Fin.ext (by simp only [Fin.val_castSucc]; omega)
    have hsucc : i.succ = Fin.last (t + 2) :=
      Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
    refine (FlipFrame.elt_eq_elt_iff_last hσ.invol (m := t + 2) (by omega)
      (c := (oddEmb hσ hM hinj hrange hφ hOdd x).toFlipFrame)
      (d := (oddEmb hσ hM hinj hrange hφ hOdd y).toFlipFrame)).mpr ⟨?_, ?_⟩
    · intro j hjlt
      have hj : j ≠ Fin.last (t + 2) := by
        intro h
        have hval := congrArg Fin.val h
        simp only [Fin.val_last] at hval
        omega
      have hj1 : j ≠ i.castSucc := by
        intro h
        rw [hcast] at h
        have hval := congrArg Fin.val h
        have hval1 : (⟨t + 1, by omega⟩ : Fin (t + 3)).val = t + 1 := rfl
        rw [hval1] at hval
        omega
      have hj2 : j ≠ i.succ := by
        intro h
        rw [hsucc] at h
        have hval := congrArg Fin.val h
        simp only [Fin.val_last] at hval
        omega
      rw [oddEmb_line_of_ne hσ hM hinj hrange hφ hOdd x hj,
        oddEmb_line_of_ne hσ hM hinj hrange hφ hOdd y hj, hxy j hj1 hj2]
    · have hplane := adj_sup_eq hσ hxy
      rw [hcast, hsucc] at hplane
      have hne' : (⟨t + 2 - 1, by omega⟩ : Fin (t + 3)) ≠ Fin.last (t + 2) := by
        intro h
        have hval := congrArg Fin.val h
        simp only [Fin.val_last] at hval
        omega
      rw [oddEmb_line_of_ne hσ hM hinj hrange hφ hOdd x hne',
        oddEmb_line_last hσ hM hinj hrange hφ hOdd x,
        oddEmb_line_of_ne hσ hM hinj hrange hφ hOdd y hne',
        oddEmb_line_last hσ hM hinj hrange hφ hOdd y,
        dFlipSub_dFlipSub hσ.invol, dFlipSub_dFlipSub hσ.invol,
        map_sup_map, map_sup_map]
      exact congrArg (fun W => W.map φ) hplane
  · have hτ : solidTypeB t i = i.castSucc := by
      unfold solidTypeB
      rw [if_neg hi]
    rw [hτ]
    refine (FlipFrame.elt_eq_elt_iff_castSucc hσ.invol (k := i)
      (c := (oddEmb hσ hM hinj hrange hφ hOdd x).toFlipFrame)
      (d := (oddEmb hσ hM hinj hrange hφ hOdd y).toFlipFrame)).mpr ⟨?_, ?_⟩
    · intro j hj1 hj2
      by_cases hj : j = Fin.last (t + 2)
      · rw [hj, oddEmb_line_last hσ hM hinj hrange hφ hOdd x,
          oddEmb_line_last hσ hM hinj hrange hφ hOdd y]
        have hlast1 : Fin.last (t + 2) ≠ i.castSucc := by
          intro h
          have hval := congrArg Fin.val h
          simp only [Fin.val_last, Fin.val_castSucc] at hval
          omega
        have hlast2 : Fin.last (t + 2) ≠ i.succ := by
          intro h
          have hval := congrArg Fin.val h
          simp only [Fin.val_last, Fin.val_succ] at hval
          omega
        rw [hxy (Fin.last (t + 2)) hlast1 hlast2]
      · rw [oddEmb_line_of_ne hσ hM hinj hrange hφ hOdd x hj,
          oddEmb_line_of_ne hσ hM hinj hrange hφ hOdd y hj, hxy j hj1 hj2]
    · have hplane := adj_sup_eq hσ hxy
      have hcast1 : i.castSucc ≠ Fin.last (t + 2) := by
        intro h
        have hval := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_last] at hval
        omega
      have hsucc1 : i.succ ≠ Fin.last (t + 2) := by
        intro h
        have hval := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_last] at hval
        omega
      rw [oddEmb_line_of_ne hσ hM hinj hrange hφ hOdd x hcast1,
        oddEmb_line_of_ne hσ hM hinj hrange hφ hOdd y hcast1,
        oddEmb_line_of_ne hσ hM hinj hrange hφ hOdd x hsucc1,
        oddEmb_line_of_ne hσ hM hinj hrange hφ hOdd y hsucc1,
        map_sup_map, map_sup_map, hplane]

private noncomputable def oddAuxLine (d : DChamber σ (t + 3)) (j : Fin (t + 3)) :
    Submodule K (Fin (t + 3) ⊕ Fin (t + 3) → K) :=
  if j = Fin.last (t + 2) then dFlipSub σ (d.line j) else d.line j

private theorem oddEmb_elt_fork (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x)
    (hOdd : ¬ Even ((t + 3) - Module.finrank K ↥(M ⊓ stdLag (t + 3) K)))
    (c : Frame σ (t + 3)) :
    (oddEmb hσ hM hinj hrange hφ hOdd c).elt (⟨t + 1, by omega⟩ : Fin (t + 3)) = M := by
  rw [FlipFrame.elt_of_add_one_eq (c := (oddEmb hσ hM hinj hrange hφ hOdd c).toFlipFrame)
    (i := (⟨t + 1, by omega⟩ : Fin (t + 3))) (by simp)]
  exact oddEmb_alt hσ hM hinj hrange hφ hOdd c

private theorem dChamber_elt_fork (d : DChamber σ (t + 3)) :
    d.elt (⟨t + 1, by omega⟩ : Fin (t + 3)) = d.alt :=
  FlipFrame.elt_of_add_one_eq (c := d.toFlipFrame)
    (i := (⟨t + 1, by omega⟩ : Fin (t + 3))) (by simp)

private theorem oddNeighbour_alt (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x)
    (hOdd : ¬ Even ((t + 3) - Module.finrank K ↥(M ⊓ stdLag (t + 3) K)))
    (i : Fin (t + 2)) (x : Frame σ (t + 3)) (d : DChamber σ (t + 3))
    (hadj : ∀ j : Fin (t + 3), j ≠ solidTypeB t i →
      (oddEmb hσ hM hinj hrange hφ hOdd x).elt j = d.elt j) :
    d.alt = M := by
  have hib := i.is_lt
  have hj0 : (⟨t + 1, by omega⟩ : Fin (t + 3)) ≠ solidTypeB t i := by
    intro h
    have hval := congrArg Fin.val h
    have hval0 : (⟨t + 1, by omega⟩ : Fin (t + 3)).val = t + 1 := rfl
    rw [hval0] at hval
    by_cases hi : (i : ℕ) + 1 = t + 2
    · rw [show solidTypeB t i = Fin.last (t + 2) from by unfold solidTypeB; rw [if_pos hi]] at hval
      have hv : (Fin.last (t + 2) : Fin (t + 3)).val = t + 2 := rfl
      rw [hv] at hval
      omega
    · rw [show solidTypeB t i = i.castSucc from by unfold solidTypeB; rw [if_neg hi]] at hval
      have hv : (i.castSucc : Fin (t + 3)).val = (i : ℕ) := rfl
      rw [hv] at hval
      omega
  have h := hadj (⟨t + 1, by omega⟩ : Fin (t + 3)) hj0
  rw [oddEmb_elt_fork hσ hM hinj hrange hφ hOdd x, dChamber_elt_fork d] at h
  exact h.symm

private theorem sub_le_alt (d : DChamber σ (t + 3)) : d.sub (t + 2) ≤ d.alt := by
  rw [FlipFrame.alt]
  exact le_sup_left

private theorem dFlipSub_line_le_alt (d : DChamber σ (t + 3)) :
    dFlipSub σ (d.line (Fin.last (t + 2))) ≤ d.alt := by
  rw [FlipFrame.alt]
  exact le_sup_right

private theorem oddAuxLine_le (d : DChamber σ (t + 3)) (halt : d.alt = M) :
    ∀ j, oddAuxLine d j ≤ M := by
  intro j
  by_cases hj : j = Fin.last (t + 2)
  · subst hj
    rw [oddAuxLine, if_pos rfl]
    exact le_trans (dFlipSub_line_le_alt d) (le_of_eq halt)
  · have hjlt : (j : ℕ) < t + 2 := by
      have h := j.is_lt
      have hne : (j : ℕ) ≠ t + 2 := fun h' => hj (Fin.ext h')
      omega
    rw [oddAuxLine, if_neg hj]
    exact le_trans (le_trans (d.line_le_sub (l := j) hjlt) (sub_le_alt d)) (le_of_eq halt)

private theorem oddAuxLine_isFlipflopPt (hσ : IsUnitaryInvolution σ) (d : DChamber σ (t + 3)) :
    ∀ j, IsFlipflopPt σ (oddAuxLine d j) := by
  intro j
  by_cases hj : j = Fin.last (t + 2)
  · rw [oddAuxLine, if_pos hj]
    exact isFlipflopPt_dFlipSub hσ.invol (d.isFlipflopPt_line j)
  · rw [oddAuxLine, if_neg hj]
    exact d.isFlipflopPt_line j

private theorem oddAuxLine_orth (hσ : ∀ x, σ (σ x) = x) (d : DChamber σ (t + 3)) :
    ∀ i j, i ≠ j → ∀ u ∈ oddAuxLine d i, ∀ v ∈ oddAuxLine d j, flipHerm σ u v = 0 := by
  intro i j hij u hu v hv
  by_cases hi : i = Fin.last (t + 2)
  · subst hi
    have hj : j ≠ Fin.last (t + 2) := Ne.symm hij
    rw [oddAuxLine, if_pos rfl] at hu
    rw [oddAuxLine, if_neg hj] at hv
    have hdu : dFlip σ u ∈ d.line (Fin.last (t + 2)) := (mem_dFlipSub hσ).mp hu
    have hu_eq : u = dFlip σ (dFlip σ u) := (dFlip_dFlip hσ u).symm
    rw [hu_eq, flipHerm, polar_dFlip, d.polar_eq_zero (Fin.last (t + 2)) j (Ne.symm hj)
      (dFlip σ u) hdu v hv, map_zero]
  · by_cases hj : j = Fin.last (t + 2)
    · subst hj
      rw [oddAuxLine, if_neg hi] at hu
      rw [oddAuxLine, if_pos rfl] at hv
      have hdv : dFlip σ v ∈ d.line (Fin.last (t + 2)) := (mem_dFlipSub hσ).mp hv
      have hv_eq : v = dFlip σ (dFlip σ v) := (dFlip_dFlip hσ v).symm
      rw [hv_eq, flipHerm, dFlip_dFlip hσ]
      exact d.polar_eq_zero i (Fin.last (t + 2)) hi u hu (dFlip σ v) hdv
    · rw [oddAuxLine, if_neg hi] at hu
      rw [oddAuxLine, if_neg hj] at hv
      exact d.flipHerm_eq_zero i j hij u hu v hv

private noncomputable def oddAuxFrame (hσ : IsUnitaryInvolution σ)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x)
    (d : DChamber σ (t + 3)) (halt : d.alt = M) : Frame σ (t + 3) :=
  comapFrame hσ.invol hinj hrange hφ (oddAuxLine_le d halt)
    (oddAuxLine_isFlipflopPt hσ d) (oddAuxLine_orth hσ.invol d)

private theorem oddAuxFrame_map (hσ : IsUnitaryInvolution σ)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x)
    (d : DChamber σ (t + 3)) (halt : d.alt = M) (j : Fin (t + 3)) :
    ((oddAuxFrame hσ hinj hrange hφ d halt).line j).map φ = oddAuxLine d j :=
  comap_map_eq_of_le hrange (oddAuxLine_le d halt j)

private theorem oddEmb_isPanelLift (hσ : IsUnitaryInvolution σ) (hM : IsSolid σ M)
    (hinj : Function.Injective φ) (hrange : LinearMap.range φ = M)
    (hφ : ∀ x y, flipHerm σ (φ x) (φ y) = herm σ y x)
    (hOdd : ¬ Even ((t + 3) - Module.finrank K ↥(M ⊓ stdLag (t + 3) K))) :
    IsPanelLift (frameSystem σ (t + 2)) (dChamberSystem σ (t + 2))
      (solidTypeB t) (oddEmb hσ hM hinj hrange hφ hOdd) := by
  intro i x d hadj
  rw [dChamberSystem_adj_iff] at hadj
  have hib := i.is_lt
  have halt := oddNeighbour_alt hσ hM hinj hrange hφ hOdd i x d hadj
  let y := oddAuxFrame hσ hinj hrange hφ d halt
  have hyline := oddAuxFrame_map hσ hinj hrange hφ d halt
  have hemb : oddEmb hσ hM hinj hrange hφ hOdd y = d := by
    apply DChamber.ext
    funext j
    by_cases hj : j = Fin.last (t + 2)
    · rw [hj, oddEmb_line_last, hyline (Fin.last (t + 2)), oddAuxLine, if_pos rfl,
        dFlipSub_dFlipSub hσ.invol]
    · rw [oddEmb_line_of_ne hσ hM hinj hrange hφ hOdd y hj, hyline j, oddAuxLine, if_neg hj]
  have hyadj : (frameSystem σ (t + 2)).adj i x y := by
    intro j hj1 hj2
    refine Submodule.map_injective_of_injective hinj ?_
    by_cases hi : (i : ℕ) + 1 = t + 2
    · have hτ : solidTypeB t i = Fin.last (t + 2) := by
        unfold solidTypeB
        rw [if_pos hi]
      have hadjLast : ∀ j : Fin (t + 3), j ≠ Fin.last (t + 2) →
          (oddEmb hσ hM hinj hrange hφ hOdd x).elt j = d.elt j := by
        intro j hj
        exact hadj j (by rw [hτ]; exact hj)
      have hlines := (FlipFrame.elt_eq_elt_iff_last hσ.invol (m := t + 2) (by omega)
        (c := (oddEmb hσ hM hinj hrange hφ hOdd x).toFlipFrame)
        (d := d.toFlipFrame)).mp hadjLast
      have hsucc : i.succ = Fin.last (t + 2) :=
        Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
      have hcast : (i.castSucc : Fin (t + 3)) = (⟨t + 1, by omega⟩ : Fin (t + 3)) :=
        Fin.ext (by simp only [Fin.val_castSucc]; omega)
      have hjlast : j ≠ Fin.last (t + 2) := by
        intro h
        exact hj2 (h.trans hsucc.symm)
      have hjlt : (j : ℕ) + 1 < t + 2 := by
        have hv1 : (j : ℕ) ≠ t + 1 := by
          intro h
          apply hj1
          apply Fin.ext
          rw [hcast]
          exact h
        have hv2 : (j : ℕ) ≠ t + 2 := by
          intro h
          apply hj2
          apply Fin.ext
          rw [hsucc, Fin.val_last]
          exact h
        have hjlt' := j.is_lt
        omega
      rw [show (x.line j).map φ = (oddEmb hσ hM hinj hrange hφ hOdd x).line j from
          (oddEmb_line_of_ne hσ hM hinj hrange hφ hOdd x hjlast).symm,
        hlines.1 j hjlt, hyline j, oddAuxLine, if_neg hjlast]
    · have hτ : solidTypeB t i = i.castSucc := by
        unfold solidTypeB
        rw [if_neg hi]
      have hadjCast : ∀ j : Fin (t + 3), j ≠ i.castSucc →
          (oddEmb hσ hM hinj hrange hφ hOdd x).elt j = d.elt j := by
        intro j hj
        exact hadj j (by rw [hτ]; exact hj)
      have hlines := (FlipFrame.elt_eq_elt_iff_castSucc hσ.invol (k := i)
        (c := (oddEmb hσ hM hinj hrange hφ hOdd x).toFlipFrame)
        (d := d.toFlipFrame)).mp hadjCast
      by_cases hj : j = Fin.last (t + 2)
      · subst hj
        have hlast1 : Fin.last (t + 2) ≠ i.castSucc := by
          intro h
          have hval := congrArg Fin.val h
          simp only [Fin.val_last, Fin.val_castSucc] at hval
          omega
        have hlast2 : Fin.last (t + 2) ≠ i.succ := by
          intro h
          have hval := congrArg Fin.val h
          simp only [Fin.val_last, Fin.val_succ] at hval
          omega
        have heq : (x.line (Fin.last (t + 2))).map φ =
            dFlipSub σ (d.line (Fin.last (t + 2))) := by
          have h := hlines.1 (Fin.last (t + 2)) hlast1 hlast2
          rw [oddEmb_line_last hσ hM hinj hrange hφ hOdd x] at h
          rw [← h, dFlipSub_dFlipSub hσ.invol]
        rw [heq, hyline (Fin.last (t + 2)), oddAuxLine, if_pos rfl]
      · rw [show (x.line j).map φ = (oddEmb hσ hM hinj hrange hφ hOdd x).line j from
            (oddEmb_line_of_ne hσ hM hinj hrange hφ hOdd x hj).symm,
          hlines.1 j hj1 hj2, hyline j, oddAuxLine, if_neg hj]
  exact ⟨y, hyadj, hemb⟩

theorem IsSolid.exists_solidChart (hσ : IsUnitaryInvolution σ) {t : ℕ}
    {M : Submodule K (Fin (t + 3) ⊕ Fin (t + 3) → K)} (hM : IsSolid σ M) :
    ∃ chart : SolidChart σ t M, Function.Injective chart.emb ∧
      IsTypeMorphism (frameSystem σ (t + 2)) (dChamberSystem σ (t + 2)) chart.τ chart.emb ∧
      IsPanelLift (frameSystem σ (t + 2)) (dChamberSystem σ (t + 2)) chart.τ chart.emb := by
  obtain ⟨φ, hinj, hrange, hφ⟩ := hM.exists_coord hσ
  by_cases hEven : Even ((t + 3) - Module.finrank K ↥(M ⊓ stdLag (t + 3) K))
  · have hτinj : Function.Injective (fun i : Fin (t + 2) => (i.castSucc : Fin (t + 3))) := by
      intro i j hij
      exact Fin.ext (by simpa using congrArg Fin.val hij)
    refine ⟨⟨φ, hinj, hrange, hφ, (fun i : Fin (t + 2) => (i.castSucc : Fin (t + 3))),
      hτinj, rfl, evenEmb hσ hM hinj hrange hφ hEven, fun _ => rfl⟩, ?_, ?_, ?_⟩
    · intro x y h
      apply Frame.ext
      funext j
      have hline := congrFun (congrArg (fun c : DChamber σ (t + 3) => c.line) h) j
      rw [evenEmb_line hσ hM hinj hrange hφ hEven x,
        evenEmb_line hσ hM hinj hrange hφ hEven y] at hline
      exact Submodule.map_injective_of_injective hinj hline
    · exact evenEmb_isTypeMorphism hσ hM hinj hrange hφ hEven
    · exact evenEmb_isPanelLift hσ hM hinj hrange hφ hEven
  · have hline0 : ∀ c : Frame σ (t + 3),
        (oddEmb hσ hM hinj hrange hφ hEven c).line 0 = (c.line 0).map φ := by
      intro c
      exact oddEmb_line_of_ne hσ hM hinj hrange hφ hEven c (by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_last, Fin.val_zero] at hv
        omega)
    refine ⟨⟨φ, hinj, hrange, hφ, solidTypeB t, solidTypeB_injective t, solidTypeB_zero t,
      oddEmb hσ hM hinj hrange hφ hEven, hline0⟩, ?_, ?_, ?_⟩
    · intro x y h
      have hline : ∀ j, (oddEmb hσ hM hinj hrange hφ hEven x).line j =
          (oddEmb hσ hM hinj hrange hφ hEven y).line j := fun j =>
        congrFun (congrArg (fun c : DChamber σ (t + 3) => c.line) h) j
      apply Frame.ext
      funext j
      by_cases hj : j = Fin.last (t + 2)
      · subst hj
        have h := hline (Fin.last (t + 2))
        rw [oddEmb_line_last hσ hM hinj hrange hφ hEven x,
          oddEmb_line_last hσ hM hinj hrange hφ hEven y] at h
        have h' := congrArg (dFlipSub σ) h
        rw [dFlipSub_dFlipSub hσ.invol, dFlipSub_dFlipSub hσ.invol] at h'
        exact Submodule.map_injective_of_injective hinj h'
      · have h := hline j
        rw [oddEmb_line_of_ne hσ hM hinj hrange hφ hEven x hj,
          oddEmb_line_of_ne hσ hM hinj hrange hφ hEven y hj] at h
        exact Submodule.map_injective_of_injective hinj h
    · show IsTypeMorphism (frameSystem σ (t + 2)) (dChamberSystem σ (t + 2))
        (solidTypeB t) (oddEmb hσ hM hinj hrange hφ hEven)
      exact oddEmb_isTypeMorphism hσ hM hinj hrange hφ hEven
    · show IsPanelLift (frameSystem σ (t + 2)) (dChamberSystem σ (t + 2))
        (solidTypeB t) (oddEmb hσ hM hinj hrange hφ hEven)
      exact oddEmb_isPanelLift hσ hM hinj hrange hφ hEven
