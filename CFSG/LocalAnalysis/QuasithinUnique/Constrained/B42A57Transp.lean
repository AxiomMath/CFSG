module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57E7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57M5Cyc
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.QuasithinUnique.B42A57

open CFSG.Quasithin Multiplicative Equiv

section Disp

variable {S : Type} [CommGroup S]

@[expose] def Disp (t : MulAut S) : Set S := {w | ∃ s, w = t s * s⁻¹}

theorem Disp_conj (g t : MulAut S) : Disp (g * t * g⁻¹) = g '' Disp t := by
  ext w
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨t (g⁻¹ s) * (g⁻¹ s)⁻¹, ⟨g⁻¹ s, rfl⟩, ?_⟩
    simp [MulAut.mul_apply]
  · rintro ⟨d, ⟨s, rfl⟩, rfl⟩
    refine ⟨g s, ?_⟩
    simp [MulAut.mul_apply]

theorem fixed_of_mem_Disp {t : MulAut S} (ht : t * t = 1) (hS : ∀ s : S, s * s = 1) {d : S}
    (hd : d ∈ Disp t) : t d = d := by
  obtain ⟨s, rfl⟩ := hd
  have h1 : t (t s) = s := by
    have := congrArg (fun f : MulAut S => f s) ht
    simpa [MulAut.mul_apply] using this
  have h2 : t (t s * s⁻¹) = (t s * s⁻¹)⁻¹ := by
    rw [map_mul, map_inv, h1, mul_inv_rev, inv_inv, mul_comm]
  rw [h2]
  exact inv_eq_of_mul_eq_one_right (hS _)

theorem sq_eq_one_of_same_center {t₁ t₂ : MulAut S}
    (hS : ∀ s : S, s * s = 1) {w : S} (hd1 : Disp t₁ ⊆ {1, w}) (hd2 : Disp t₂ ⊆ {1, w})
    (hw1 : t₁ w = w) (hw2 : t₂ w = w) : (t₁ * t₂) * (t₁ * t₂) = 1 := by
  apply MulEquiv.ext
  intro s
  set c : S := (t₁ * t₂) s * s⁻¹ with hc
  have hcmem : c = 1 ∨ c = w := by
    have e1 : t₂ s * s⁻¹ = 1 ∨ t₂ s * s⁻¹ = w := by
      have := hd2 ⟨s, rfl⟩
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    have e2 : t₁ (t₂ s) * (t₂ s)⁻¹ = 1 ∨ t₁ (t₂ s) * (t₂ s)⁻¹ = w := by
      have := hd1 ⟨t₂ s, rfl⟩
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    have hcdef : c = (t₁ (t₂ s) * (t₂ s)⁻¹) * (t₂ s * s⁻¹) := by
      rw [hc, MulAut.mul_apply]
      group
    rw [hcdef]
    rcases e1 with h | h <;> rcases e2 with h' | h' <;> rw [h, h']
    · left; simp
    · right; simp
    · right; simp
    · left; exact hS w
  have hct : (t₁ * t₂) c = c := by
    rcases hcmem with h | h <;> rw [h]
    · simp
    · rw [MulAut.mul_apply, hw2, hw1]
  have hv : (t₁ * t₂) s = c * s := by rw [hc]; group
  show (t₁ * t₂) ((t₁ * t₂) s) = s
  rw [hv, map_mul, hct, hv, ← mul_assoc, hS c, one_mul]

end Disp

section Rho

variable {S : Type} [CommGroup S] (ρ : Equiv.Perm (Fin 7) →* MulAut S)

@[expose] def gOf (i j : Fin 7) : Equiv.Perm (Fin 7) := swap (swap 0 i 1) j * swap 0 i

theorem gOf_zero : ∀ i j : Fin 7, i ≠ j → gOf i j 0 = i := by decide

theorem gOf_one : ∀ i j : Fin 7, i ≠ j → gOf i j 1 = j := by decide

theorem three_cycle_ne : ∀ i j k : Fin 7, i ≠ j → j ≠ k → i ≠ k →
    (swap i k * swap j k) * (swap i k * swap j k) ≠ 1 := by decide

@[expose] def W (ρ : Equiv.Perm (Fin 7) →* MulAut S) (w₀ : S) (i j : Fin 7) : S :=
  ρ (gOf i j) w₀

theorem W_def (ρ : Equiv.Perm (Fin 7) →* MulAut S) (w₀ : S) (i j : Fin 7) :
    W ρ w₀ i j = ρ (gOf i j) w₀ := rfl

structure TransvData (w₀ : S) : Prop where
  inj : Function.Injective ρ
  exp : ∀ s : S, s * s = 1
  ne : w₀ ≠ 1
  disp : Disp (ρ (swap 0 1)) = {1, w₀}

variable {ρ} {w₀ : S} (T : TransvData ρ w₀)

include T

theorem fix_w₀ (h : Equiv.Perm (Fin 7)) (hh : swap (h 0) (h 1) = swap 0 1) : ρ h w₀ = w₀ := by
  have e : h * swap 0 1 * h⁻¹ = swap 0 1 := by rw [← Equiv.swap_apply_apply, hh]
  have hD : Disp (ρ (swap 0 1)) = ρ h '' Disp (ρ (swap 0 1)) := by
    have := Disp_conj (ρ h) (ρ (swap 0 1))
    rw [← map_inv, ← map_mul, ← map_mul, e] at this
    exact this
  have hmem : ρ h w₀ ∈ Disp (ρ (swap 0 1)) := by
    rw [hD]
    exact ⟨w₀, by rw [T.disp]; exact Or.inr rfl, rfl⟩
  rw [T.disp] at hmem
  rcases hmem with h1 | h1
  · exfalso
    apply T.ne
    apply (ρ h).injective
    rw [map_one]
    exact h1
  · exact h1


theorem W_eq (g : Equiv.Perm (Fin 7)) : ρ g w₀ = W ρ w₀ (g 0) (g 1) := by
  have hij : g 0 ≠ g 1 := fun h => by simpa using g.injective h
  set h : Equiv.Perm (Fin 7) := (gOf (g 0) (g 1))⁻¹ * g with hh
  have h0 : h 0 = 0 := by
    rw [hh, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq, gOf_zero _ _ hij]
  have h1 : h 1 = 1 := by
    rw [hh, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq, gOf_one _ _ hij]
  have hfix := fix_w₀ T h (by rw [h0, h1])
  have : g = gOf (g 0) (g 1) * h := by rw [hh]; group
  rw [W_def, this, map_mul, MulAut.mul_apply, hfix]
  congr 2
  rw [hh]; group

theorem W_perm (σ : Equiv.Perm (Fin 7)) (i j : Fin 7) (hij : i ≠ j) :
    ρ σ (W ρ w₀ i j) = W ρ w₀ (σ i) (σ j) := by
  rw [W_def, ← MulAut.mul_apply, ← map_mul, W_eq T, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    gOf_zero _ _ hij, gOf_one _ _ hij]

theorem W_symm (i j : Fin 7) (hij : i ≠ j) : W ρ w₀ i j = W ρ w₀ j i := by
  have h1 : ρ (gOf i j * swap 0 1) w₀ = W ρ w₀ i j := by
    rw [map_mul, MulAut.mul_apply, fix_w₀ T (swap 0 1) (by simp [Equiv.swap_comm]), W_def]
  have h2 := W_eq T (gOf i j * swap 0 1)
  rw [h1] at h2
  rw [h2, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
    gOf_zero _ _ hij, gOf_one _ _ hij]

theorem W_ne_one (i j : Fin 7) : W ρ w₀ i j ≠ 1 := by
  intro h
  apply T.ne
  apply (ρ (gOf i j)).injective
  rw [map_one]
  exact h

theorem disp_swap (i j : Fin 7) (hij : i ≠ j) : Disp (ρ (swap i j)) = {1, W ρ w₀ i j} := by
  have e : swap i j = gOf i j * swap 0 1 * (gOf i j)⁻¹ := by
    rw [← Equiv.swap_apply_apply, gOf_zero _ _ hij, gOf_one _ _ hij]
  rw [e, map_mul, map_mul, map_inv, Disp_conj, T.disp, Set.image_pair, map_one]
  rfl

theorem rel (i j k : Fin 7) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    W ρ w₀ i k = W ρ w₀ i j * W ρ w₀ j k := by
  have haj : swap i j j = i := Equiv.swap_apply_right i j
  have hak : swap i j k = k := Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm
  have hWik : W ρ w₀ i k = ρ (swap i j) (W ρ w₀ j k) := by
    rw [W_perm T (swap i j) j k hjk, haj, hak]
  have hmem : ρ (swap i j) (W ρ w₀ j k) * (W ρ w₀ j k)⁻¹ ∈ Disp (ρ (swap i j)) :=
    ⟨W ρ w₀ j k, rfl⟩
  rw [disp_swap T i j hij] at hmem
  rcases hmem with h1 | h1
  · exfalso
    have hfix : ρ (swap i j) (W ρ w₀ j k) = W ρ w₀ j k := mul_inv_eq_one.1 h1
    have hsame : W ρ w₀ i k = W ρ w₀ j k := by rw [hWik, hfix]
    have hinv : ∀ a b : Fin 7, ρ (swap a b) * ρ (swap a b) = 1 := fun a b => by
      rw [← map_mul, Equiv.swap_mul_self, map_one]
    have hd1 : Disp (ρ (swap i k)) = {1, W ρ w₀ j k} := by
      rw [disp_swap T i k hik, hsame]
    have hd2 : Disp (ρ (swap j k)) = {1, W ρ w₀ j k} := disp_swap T j k hjk
    have hw1 : ρ (swap i k) (W ρ w₀ j k) = W ρ w₀ j k :=
      fixed_of_mem_Disp (hinv i k) T.exp (by rw [hd1]; exact Or.inr rfl)
    have hw2 : ρ (swap j k) (W ρ w₀ j k) = W ρ w₀ j k :=
      fixed_of_mem_Disp (hinv j k) T.exp (by rw [hd2]; exact Or.inr rfl)
    have hsq := sq_eq_one_of_same_center T.exp (t₁ := ρ (swap i k)) (t₂ := ρ (swap j k))
      (by rw [hd1]) (by rw [hd2]) hw1 hw2
    apply three_cycle_ne i j k hij hjk hik
    apply T.inj
    rw [map_one]
    simp only [map_mul]
    exact hsq
  · have := mul_inv_eq_iff_eq_mul.1 h1
    rw [hWik, this]

end Rho

section Phi

variable {S : Type} [CommGroup S] {ρ : Equiv.Perm (Fin 7) →* MulAut S} {w₀ : S}

@[expose] def W0 (ρ : Equiv.Perm (Fin 7) →* MulAut S) (w₀ : S) (j : Fin 7) : S :=
  if j = 0 then 1 else W ρ w₀ 0 j

@[expose] def Phi (ρ : Equiv.Perm (Fin 7) →* MulAut S) (w₀ : S) (v : Fin 7 → ZMod 2) : S :=
  ∏ j, bp (W0 ρ w₀ j) (v j)

theorem Phi_add (T : TransvData ρ w₀) (v v' : Fin 7 → ZMod 2) :
    Phi ρ w₀ (v + v') = Phi ρ w₀ v * Phi ρ w₀ v' := by
  unfold Phi
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => bp_add (T.exp _) _ _

theorem Phi_zero : Phi ρ w₀ 0 = 1 := by
  unfold Phi
  exact Finset.prod_eq_one fun j _ => by simp [bp]

theorem pairVec_perm (σ : Equiv.Perm (Fin 7)) (a b : Fin 7) :
    (fun i => pairVec a b (σ⁻¹ i)) = pairVec (σ a) (σ b) := by
  funext i
  simp [pairVec, Pi.single_apply, Equiv.symm_apply_eq]

theorem Phi_pair (T : TransvData ρ w₀) (a b : Fin 7) (hab : a ≠ b) :
    Phi ρ w₀ (pairVec a b) = W ρ w₀ a b := by
  have h1 : Phi ρ w₀ (pairVec a b) = bp (W0 ρ w₀ a) (pairVec a b a) * bp (W0 ρ w₀ b) (pairVec a b b) :=
    Finset.prod_eq_mul a b hab (fun c _ hc => by
      have : pairVec a b c = 0 := by simp [pairVec, hc.1, hc.2]
      rw [this]; simp [bp])
      (fun h => absurd (Finset.mem_univ a) h) (fun h => absurd (Finset.mem_univ b) h)
  have ha : pairVec a b a = 1 := by simp [pairVec, hab]
  have hb : pairVec a b b = 1 := by simp [pairVec, hab.symm]
  have hone : (1 : ZMod 2) ≠ 0 := by decide
  rw [h1, ha, hb]
  simp [bp, hone]
  by_cases ha0 : a = 0
  · subst ha0
    simp [W0, hab.symm]
  · by_cases hb0 : b = 0
    · subst hb0
      simp [W0, ha0, W_symm T a 0 ha0]
    · simp only [W0, ha0, hb0, ite_false]
      rw [rel T a 0 b ha0 (Ne.symm hb0) hab, W_symm T a 0 ha0]

theorem Phi_perm_pair (T : TransvData ρ w₀) (σ : Equiv.Perm (Fin 7)) (a b : Fin 7) :
    Phi ρ w₀ (fun i => pairVec a b (σ⁻¹ i)) = ρ σ (Phi ρ w₀ (pairVec a b)) := by
  by_cases hab : a = b
  · subst hab
    have h0 : pairVec a a = 0 := pairVec_self a
    rw [h0]
    have : (fun i => (0 : Fin 7 → ZMod 2) (σ⁻¹ i)) = 0 := rfl
    rw [this, Phi_zero, map_one]
  · rw [pairVec_perm, Phi_pair T _ _ (σ.injective.ne hab), Phi_pair T _ _ hab, W_perm T σ a b hab]

theorem Phi_equiv (T : TransvData ρ w₀) (σ : Equiv.Perm (Fin 7)) (v : Fin 7 → ZMod 2)
    (hv : ∑ i, v i = 0) :
    Phi ρ w₀ (fun i => v (σ⁻¹ i)) = ρ σ (Phi ρ w₀ v) := by
  have key : ∀ l : List (Fin 7 × Fin 7),
      Phi ρ w₀ (fun i => ((l.map fun pr => pairVec pr.1 pr.2).sum) (σ⁻¹ i)) =
        ρ σ (Phi ρ w₀ ((l.map fun pr => pairVec pr.1 pr.2).sum)) := by
    intro l
    induction l with
    | nil =>
      simp only [List.map_nil, List.sum_nil]
      have : (fun i => (0 : Fin 7 → ZMod 2) (σ⁻¹ i)) = 0 := rfl
      rw [this, Phi_zero, map_one]
    | cons pr l ih =>
      simp only [List.map_cons, List.sum_cons]
      have e : (fun i => (pairVec pr.1 pr.2 + (l.map fun pr => pairVec pr.1 pr.2).sum) (σ⁻¹ i)) =
          (fun i => pairVec pr.1 pr.2 (σ⁻¹ i)) +
            (fun i => ((l.map fun pr => pairVec pr.1 pr.2).sum) (σ⁻¹ i)) := rfl
      rw [e, Phi_add T, Phi_add T, ih, Phi_perm_pair T, map_mul]
  have := key (pairsOf v)
  rwa [sum_pairsOf v hv] at this

@[expose] def PhiHom (T : TransvData ρ w₀) : ↥(G6.coreMod 7) →* S where
  toFun v := Phi ρ w₀ (toAdd (v : G6.PermMod 7))
  map_one' := by
    show Phi ρ w₀ 0 = 1
    exact Phi_zero
  map_mul' u v := Phi_add T _ _

theorem PhiHom_apply (T : TransvData ρ w₀) (v : ↥(G6.coreMod 7)) :
    PhiHom T v = Phi ρ w₀ (toAdd (v : G6.PermMod 7)) := rfl

theorem PhiHom_perm (T : TransvData ρ w₀) (σ : Equiv.Perm (Fin 7)) (v : ↥(G6.coreMod 7)) :
    PhiHom T ⟨G6.permAct 7 σ v, G6.permAct_mem_coreMod σ v.2⟩ = ρ σ (PhiHom T v) :=
  Phi_equiv T σ _ (G6.mem_coreMod.1 v.2)

theorem pairVec_mem_coreMod (a b : Fin 7) : (ofAdd (pairVec a b) : G6.PermMod 7) ∈ G6.coreMod 7 := by
  rw [G6.mem_coreMod]
  revert a b
  decide +kernel

theorem exists_iso_coreMod (T : TransvData ρ w₀)
    (hirr : ∀ U : Subgroup S, (∀ σ ∈ alternatingGroup (Fin 7), ∀ u ∈ U, ρ σ u ∈ U) →
      U = ⊥ ∨ U = ⊤) :
    ∃ β : S ≃* ↥(G6.coreMod 7), ∀ (σ : Equiv.Perm (Fin 7)) (s : S),
      ((β (ρ σ s) : ↥(G6.coreMod 7)) : G6.PermMod 7) = G6.permAct 7 σ (β s) := by
  have hpair : PhiHom T ⟨ofAdd (pairVec 0 1), pairVec_mem_coreMod 0 1⟩ = W ρ w₀ 0 1 := by
    rw [PhiHom_apply]
    exact Phi_pair T 0 1 (by decide)
  have hW01 : W ρ w₀ 0 1 ≠ 1 := W_ne_one T 0 1
  have hinj : Function.Injective (PhiHom T) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    set K : Subgroup (G6.PermMod 7) := (PhiHom T).ker.map (G6.coreMod 7).subtype with hK
    have hKle : K ≤ G6.coreMod 7 := by
      rintro _ ⟨v, _, rfl⟩
      exact v.2
    have hKinv : ∀ σ ∈ alternatingGroup (Fin 7), ∀ u ∈ K, G6.permAct 7 σ u ∈ K := by
      rintro σ _ u ⟨v, hv, rfl⟩
      refine ⟨⟨G6.permAct 7 σ v, G6.permAct_mem_coreMod σ v.2⟩, ?_, rfl⟩
      have hv1 : PhiHom T v = 1 := hv
      show PhiHom T ⟨G6.permAct 7 σ v, G6.permAct_mem_coreMod σ v.2⟩ = 1
      rw [PhiHom_perm, hv1, map_one]
    rcases coreMod7_irreducible K hKle hKinv with h | h
    · refine eq_bot_iff.2 fun v hv => ?_
      have hvK : (v : G6.PermMod 7) ∈ K := ⟨v, hv, rfl⟩
      rw [h, Subgroup.mem_bot] at hvK
      exact Subgroup.mem_bot.2 (Subtype.ext hvK)
    · exfalso
      have hmem : (ofAdd (pairVec 0 1) : G6.PermMod 7) ∈ K := by
        rw [h]; exact pairVec_mem_coreMod 0 1
      obtain ⟨v, hv, hv'⟩ := hmem
      have : v = ⟨ofAdd (pairVec 0 1), pairVec_mem_coreMod 0 1⟩ := Subtype.ext hv'
      rw [this] at hv
      have hv1 : PhiHom T ⟨ofAdd (pairVec 0 1), pairVec_mem_coreMod 0 1⟩ = 1 := hv
      rw [hpair] at hv1
      exact hW01 hv1
  have hsurj : Function.Surjective (PhiHom T) := by
    have hR : (PhiHom T).range = ⊤ := by
      rcases hirr (PhiHom T).range (by
        rintro σ _ _ ⟨v, rfl⟩
        exact ⟨⟨G6.permAct 7 σ v, G6.permAct_mem_coreMod σ v.2⟩, PhiHom_perm T σ v⟩) with h | h
      · exfalso
        have : PhiHom T ⟨ofAdd (pairVec 0 1), pairVec_mem_coreMod 0 1⟩ ∈ (PhiHom T).range :=
          ⟨_, rfl⟩
        rw [h, Subgroup.mem_bot, hpair] at this
        exact hW01 this
      · exact h
    intro s
    have : s ∈ (PhiHom T).range := by rw [hR]; trivial
    exact this
  refine ⟨(MulEquiv.ofBijective (PhiHom T) ⟨hinj, hsurj⟩).symm, fun σ s => ?_⟩
  obtain ⟨v, rfl⟩ := hsurj s
  have e1 : (MulEquiv.ofBijective (PhiHom T) ⟨hinj, hsurj⟩).symm (PhiHom T v) = v :=
    (MulEquiv.ofBijective (PhiHom T) ⟨hinj, hsurj⟩).symm_apply_apply v
  rw [e1, ← PhiHom_perm T σ v]
  have e2 : (MulEquiv.ofBijective (PhiHom T) ⟨hinj, hsurj⟩).symm
      (PhiHom T ⟨G6.permAct 7 σ v, G6.permAct_mem_coreMod σ v.2⟩) =
      ⟨G6.permAct 7 σ v, G6.permAct_mem_coreMod σ v.2⟩ :=
    (MulEquiv.ofBijective (PhiHom T) ⟨hinj, hsurj⟩).symm_apply_apply _
  rw [e2]

end Phi

end CFSG.QuasithinUnique.B42A57
