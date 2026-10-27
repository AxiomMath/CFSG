module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthMinusLift
public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthCentNode
public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthMinusRoots

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput CFSG.LieType.Steinberg.SpinFrame

variable {n : ℕ} {K : Type} [Field K] {b c : K}

@[expose] def evec (v : Fin (n - 1) ⊕ Fin (n - 1) → K) : SM n → K :=
  Sum.elim (fun a => v (.inl a)) (Sum.elim (fun a => v (.inr a)) (fun _ => 0))

theorem quad_evec (v : Fin (n - 1) ⊕ Fin (n - 1) → K) :
    quadMinus n K b c (evec v) = Qf (n - 1) v := by
  rw [quadMinus_apply]
  simp [evec, Qf]

theorem mulVec_evec (G : Matrix (SM n) (SM n) K) (lam : K)
    (hG : ∀ x y, ((∃ u, x = pl n u) ∨ (∃ u, y = pl n u)) → G x y = if x = y then lam else 0)
    (v : Fin (n - 1) ⊕ Fin (n - 1) → K) : G.mulVec (evec v) = evec ((restr G).mulVec v) := by
  funext x
  rcases x with a | a | u
  · have h1 : ∀ u : Fin 2, G (.inl a) (.inr (.inr u)) = 0 := fun u => by
      rw [show (Sum.inr (Sum.inr u) : SM n) = pl n u from rfl, hG _ _ (Or.inr ⟨u, rfl⟩)]
      simp [pl]
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, evec, restr, iota, h1]
  · have h1 : ∀ u : Fin 2, G (.inr (.inl a)) (.inr (.inr u)) = 0 := fun u => by
      rw [show (Sum.inr (Sum.inr u) : SM n) = pl n u from rfl, hG _ _ (Or.inr ⟨u, rfl⟩)]
      simp [pl]
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, evec, restr, iota, h1]
  · simp only [Matrix.mulVec, dotProduct, evec, Sum.elim_inr]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [show (Sum.inr (Sum.inr u) : SM n) = pl n u from rfl, hG _ _ (Or.inl ⟨u, rfl⟩)]
    by_cases hy : pl n u = y
    · subst hy; simp [pl, evec]
    · simp [hy]

theorem hQ_restr (k : spinGroup (quadMinus n K b c)) (lam : K)
    (hG : ∀ x y, ((∃ u, x = pl n u) ∨ (∃ u, y = pl n u)) → mat n k x y = if x = y then lam else 0)
    (v : Fin (n - 1) ⊕ Fin (n - 1) → K) :
    Qf (n - 1) ((restr (mat n k)).mulVec v) = Qf (n - 1) v := by
  have h1 := quad_evec (n := n) (b := b) (c := c) ((restr (mat n k)).mulVec v)
  have h2 := quad_evec (n := n) (b := b) (c := c) v
  rw [← h1, ← h2, ← mulVec_evec _ lam hG v]
  exact quad_mat_mulVec k (evec v)

theorem mem_PT_iff {m : ℕ} {A : Set (Fin m)} {a : Fin m} : kap a true ∈ PT A ↔ a ∈ A :=
  ⟨fun ⟨a', ha', h⟩ => (kap_inj h).1 ▸ ha', kap_true_mem_PT⟩

theorem cfg_minus (j : Fin (n - 1)) (hN : 3 ≤ n - 1) (G : Matrix (SM n) (SM n) K)
    (hLong : ∀ (a b' : Fin (n - 1)) (hab : a ≠ b') (t : Bool), a.val ≤ j.val →
      (j.val < b'.val ∨ (b'.val ≤ j.val ∧ t = true)) →
      G * mat n ((minusFrame n b c).longRoot hab true t (Multiplicative.ofAdd 1)) =
        mat n ((minusFrame n b c).longRoot hab true t (Multiplicative.ofAdd 1)) * G) :
    Cfg (restr G) (PT {a : Fin (n - 1) | a.val ≤ j.val}) := by
  refine ⟨PT_disj _, ?_, ?_⟩
  · rintro p ⟨a, ha, rfl⟩ r hr hrp
    obtain ⟨b', t, rfl⟩ := kap_surj r
    rw [bar_kap] at hr
    have ha' : a.val ≤ j.val := ha
    have hab : a ≠ b' := by
      rintro rfl
      cases t
      · exact hr (kap_true_mem_PT ha)
      · exact hrp rfl
    have hb : j.val < b'.val ∨ (b'.val ≤ j.val ∧ t = true) := by
      cases t
      · left
        by_contra hle
        exact hr (mem_PT_iff.2 (by simpa using hle))
      · by_cases hle : b'.val ≤ j.val
        · exact Or.inr ⟨hle, rfl⟩
        · exact Or.inl (by omega)
    exact hm_restr_mat (b := b) (c := c) hab t G (hLong a b' hab t ha' hb)
  · rintro p ⟨a, ha, rfl⟩
    obtain ⟨b₁, b₂, h1, h2, h12⟩ := exists_two_ne hN a
    have hr : ∀ b', b' ≠ a → bar (kap b' true) ∉ PT {a : Fin (n - 1) | a.val ≤ j.val} ∧
        kap b' true ≠ kap a true := by
      intro b' hba
      refine ⟨fun h => ?_, fun h => hba (kap_inj h).1⟩
      rw [bar_kap] at h
      obtain ⟨a', _, he⟩ := h
      obtain ⟨_, h2⟩ := kap_inj he
      simp at h2
    exact ⟨kap b₁ true, kap b₂ true, fun e => h12 (kap_inj e).1, hr b₁ h1, hr b₂ h2⟩

@[expose] def nodeSet {m : ℕ} (j : Fin m) : Set (Fin m) := {a | a.val ≤ j.val}

theorem mem_radical_of_comm_node [CharP K 2] [Finite K]
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hb : b ≠ 0) (hN : 3 ≤ n - 1) (j : Fin (n - 1))
    (hj : 1 ≤ j.val) (k : spinGroup (quadMinus n K b c))
    (hk : ∀ u ∈ CFSG.AGLEmbedding.LieOut.radical (minusDatum n hirr) j, k * u = u * k) :
    k ∈ CFSG.AGLEmbedding.LieOut.radical (minusDatum n hirr) j := by
  classical
  have hmat : ∀ u ∈ CFSG.AGLEmbedding.LieOut.radical (minusDatum n hirr) j,
      mat n k * mat n u = mat n u * mat n k := fun u hu => by
    rw [← mat_mul, ← mat_mul, hk u hu]
  have hLong : ∀ (a b' : Fin (n - 1)) (hab : a ≠ b') (t : Bool), a.val ≤ j.val →
      (j.val < b'.val ∨ (b'.val ≤ j.val ∧ t = true)) →
      mat n k * mat n ((minusFrame n b c).longRoot hab true t (Multiplicative.ofAdd 1)) =
        mat n ((minusFrame n b c).longRoot hab true t (Multiplicative.ofAdd 1)) * mat n k :=
    fun a b' hab t ha hb' => hmat _ (minusLong_mem_radical hirr j hab t ha hb' 1)
  have hShort : ∀ a : Fin (n - 1), a.val ≤ j.val → ∀ u : Fin 2,
      mat n k * mat n (twShortRoot n hirr a true (Multiplicative.ofAdd (Pi.single u 1))) =
        mat n (twShortRoot n hirr a true (Multiplicative.ofAdd (Pi.single u 1))) * mat n k :=
    fun a ha u => hmat _ (minusShort_mem_radical hirr j ha _)
  have C : Cfg (restr (mat n k)) (PT (nodeSet j)) := cfg_minus j hN (mat n k) hLong
  have PD : ∀ a : Fin (n - 1), a.val ≤ j.val → PlaneData b c (mat n k) a := by
    intro a ha
    obtain ⟨b₁, b₂, h1, h2, h12⟩ := exists_two_ne hN a
    have hr : ∀ b' : Fin (n - 1), b' ≠ a → HMS (mat n k) (minusPos n a true) (minusPos n b' true) :=
      fun b' hba => hms_of_comm b c (Ne.symm hba) true (mat n k)
        (hLong a b' (Ne.symm hba) true ha (by
          by_cases hle : b'.val ≤ j.val
          · exact Or.inr ⟨hle, rfl⟩
          · exact Or.inl (by omega)))
    have hcr := col_row_of_two (G := mat n k) (p := minusPos n a true)
      (fun e => h12 (minusPos_inj e).1) (fun e => h1 (minusPos_inj e).1.symm)
      (fun e => h2 (minusPos_inj e).1.symm) (hr b₁ h1) (hr b₂ h2)
    exact ⟨hcr.1, hcr.2, fun u => comm_entries_short_mat hirr a u (mat n k) (hShort a ha u)⟩
  have ha₁ : (⟨0, by omega⟩ : Fin (n - 1)).val ≤ j.val := by simp
  have ha₂ : (⟨1, by omega⟩ : Fin (n - 1)).val ≤ j.val := by simpa using hj
  have h12 : (⟨0, by omega⟩ : Fin (n - 1)) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hblk := block_of_two hb h12 (PD _ ha₁) (PD _ ha₂)
  have hQ := hQ_restr (b := b) (c := c) k _ hblk
  have hd := PT_disj (nodeSet j)
  have hP2 : ∀ p ∈ PT (nodeSet j), ∃ p' ∈ PT (nodeSet j), p' ≠ p := by
    rintro p ⟨a, ha, rfl⟩
    by_cases e : a = ⟨0, by omega⟩
    · exact ⟨kap ⟨1, by omega⟩ true, kap_true_mem_PT ha₂, fun h => by
        have := (kap_inj h).1
        subst e
        simp [Fin.ext_iff] at this⟩
    · exact ⟨kap ⟨0, by omega⟩ true, kap_true_mem_PT ha₁, fun h => e (kap_inj h).1.symm⟩
  have hne : (PT (nodeSet j)).Nonempty := ⟨kap ⟨0, by omega⟩ true, kap_true_mem_PT ha₁⟩
  have hl : ∀ p ∈ PT (nodeSet j), restr (mat n k) p p = 1 := by
    rintro p ⟨a, ha, rfl⟩
    by_cases hall : ∀ b' : Fin (n - 1), b' ∈ nodeSet j
    · obtain ⟨b₁, b₂, h1, h2, h12⟩ := exists_two_ne hN a
      exact C.lam_one_three hQ (p' := kap b₁ true) (p'' := kap b₂ true) (kap_true_mem_PT ha)
        (kap_true_mem_PT (hall _)) (kap_true_mem_PT (hall _))
        (fun e => h1 (kap_inj e).1.symm) (fun e => h2 (kap_inj e).1.symm)
        (fun e => h12 (kap_inj e).1)
    · obtain ⟨b₀, hb₀⟩ := not_forall.mp hall
      refine C.lam_one_free hQ (kap_true_mem_PT ha) (r := kap b₀ true) ?_ ?_ ?_ ?_
      · rw [bar_kap]
        rintro ⟨a', _, he⟩
        have := (kap_inj he).2
        simp at this
      · intro e
        exact hb₀ ((kap_inj e).1 ▸ ha)
      · intro h
        exact hb₀ (mem_PT_iff.1 h)
      · rw [bar_kap]
        intro e
        have := (kap_inj e).2
        simp at this
  have hΔ : ∀ x y, ¬ (x ∈ PT (nodeSet j) ∧ bar y ∈ PT (nodeSet j)) →
      restr (mat n k) x y = if x = y then 1 else 0 :=
    fun x y h => C.delta hQ hl hP2 hne x y h
  have hS : Shape (restr (mat n k)) (PT (nodeSet j)) :=
    ⟨hΔ, fun p hp => Cfg.alt_diag hQ hΔ hd hp, fun p hp q hq => by
      by_cases e : p = q
      · subst e
        rfl
      · exact Cfg.alt_symm hQ hΔ hd hp hq e⟩
  have hlam : mat n k (minusPos n ⟨0, by omega⟩ true) (minusPos n ⟨0, by omega⟩ true) = 1 :=
    hl _ (kap_true_mem_PT ha₁)
  have hP : PlaneId (mat n k) := fun x y h => by rw [hblk x y h, hlam]
  exact lift_minus hirr _ (nodeSet j)
    (fun a ha b' hb' hab r => minusLong_mem_radical hirr j hab true ha (Or.inr ⟨hb', rfl⟩) r)
    _ k hP hS rfl

end CFSG.HardMathSupport.Cooperstein.StructureLie
