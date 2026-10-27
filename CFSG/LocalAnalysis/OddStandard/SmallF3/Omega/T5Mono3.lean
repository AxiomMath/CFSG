module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Mono2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Sim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma exists_two_ne (i : Fin 6) :
    ∃ m1 m2 : Fin 6, m1 ≠ i ∧ m2 ≠ i ∧ m1 ≠ m2 := by
  fin_cases i
  · exact ⟨1, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide⟩

private lemma exists_ne_pair (i m : Fin 6) : ∃ k : Fin 6, k ≠ i ∧ k ≠ m := by
  revert i m
  decide

private theorem signChange_perm_mul {fr : NFrame Q (Fin 6) 1} {J : Finset (Fin 6)}
    {ρ : Equiv.Perm (Fin 6)} (hρ : J.map ρ.toEmbedding = J) :
    fr.signChange J * fr.permOrth ρ = fr.permOrth ρ * fr.signChange J := by
  have h := fr.permOrth_mul_signChange ρ J
  rw [hρ] at h
  exact h.symm

private theorem signChange_central_monoP {fr : NFrame Q (Fin 6) 1} {P : Subgroup (OGroup Q)}
    (hP : ∀ g, g ∈ P ↔ ∃ σ ∈ monoD, ∃ J : Finset (Fin 6), Even J.card ∧
      g = fr.permOrth σ * fr.signChange J)
    {J : Finset (Fin 6)} (hJ : ∀ ρ ∈ monoD, J.map ρ.toEmbedding = J) :
    ∀ h ∈ P, fr.signChange J * h = h * fr.signChange J := by
  intro h hh
  obtain ⟨ρ, hρD, K, _hK, rfl⟩ := (hP h).mp hh
  calc fr.signChange J * (fr.permOrth ρ * fr.signChange K)
      = (fr.signChange J * fr.permOrth ρ) * fr.signChange K := (mul_assoc _ _ _).symm
    _ = (fr.permOrth ρ * fr.signChange J) * fr.signChange K := by
          rw [signChange_perm_mul (fr := fr) (hJ ρ hρD)]
    _ = fr.permOrth ρ * (fr.signChange J * fr.signChange K) := mul_assoc _ _ _
    _ = fr.permOrth ρ * (fr.signChange K * fr.signChange J) := by
          rw [fr.signChange_comm J K]
    _ = (fr.permOrth ρ * fr.signChange K) * fr.signChange J := (mul_assoc _ _ _).symm

theorem NFrame.piOrth_eq_signChange_univ {ι : Type} [Fintype ι] [DecidableEq ι] {c : ZMod 3}
    (fr : NFrame Q ι c) : piOrth Q = fr.signChange Finset.univ := by
  apply Subtype.ext
  apply fr.b.ext'
  intro i
  rw [coe_piOrth_apply, fr.signChange_basis Finset.univ i, if_pos (Finset.mem_univ i)]

theorem t5_mono_center {fr : NFrame Q (Fin 6) 1} {P : Subgroup (OGroup Q)}
    (hP : ∀ g, g ∈ P ↔ ∃ σ ∈ monoD, ∃ J : Finset (Fin 6), Even J.card ∧
      g = fr.permOrth σ * fr.signChange J)
    {g : OGroup Q} (hg : g ∈ P) :
    (∀ h ∈ P, g * h = h * g) ↔
      (g = 1 ∨ g = fr.signChange {0, 1, 2, 3} ∨ g = fr.signChange {4, 5} ∨
        g = fr.signChange Finset.univ) := by
  have ht_mem : ∀ K : Finset (Fin 6), Even K.card → fr.signChange K ∈ P := by
    intro K hK
    exact (hP _).mpr ⟨1, one_mem _, K, hK, by simp [fr.permOrth_one]⟩
  have hp_mem : ∀ ρ : Equiv.Perm (Fin 6), ρ ∈ monoD → fr.permOrth ρ ∈ P := by
    intro ρ hρ
    exact (hP _).mpr ⟨ρ, hρ, ∅, by decide, by simp [fr.signChange_empty]⟩
  constructor
  · intro hc
    obtain ⟨σ, _hσD, J, _hJeven, hgeq⟩ := (hP g).mp hg
    subst hgeq
    have hfix : ∀ K : Finset (Fin 6), Even K.card → K.map σ.toEmbedding = K := by
      intro K hK
      have hcomm := hc _ (ht_mem K hK)
      have h2 : (fr.permOrth σ * fr.signChange K) * fr.signChange J =
          (fr.signChange K * fr.permOrth σ) * fr.signChange J := by
        calc (fr.permOrth σ * fr.signChange K) * fr.signChange J
            = fr.permOrth σ * (fr.signChange K * fr.signChange J) := mul_assoc _ _ _
          _ = fr.permOrth σ * (fr.signChange J * fr.signChange K) := by
                rw [fr.signChange_comm K J]
          _ = (fr.permOrth σ * fr.signChange J) * fr.signChange K :=
                (mul_assoc _ _ _).symm
          _ = fr.signChange K * (fr.permOrth σ * fr.signChange J) := hcomm
          _ = (fr.signChange K * fr.permOrth σ) * fr.signChange J :=
                (mul_assoc _ _ _).symm
      have hc' := mul_right_cancel h2
      have hp := fr.permOrth_mul_signChange σ K
      rw [hc'] at hp
      exact (fr.signChange_injective (mul_right_cancel hp)).symm
    have hσ1 : σ = 1 := by
      apply Equiv.ext
      intro i
      obtain ⟨m1, m2, hm1, hm2, hm12⟩ := exists_two_ne i
      have key : ∀ m : Fin 6, m ≠ i → σ i = i ∨ σ i = m := by
        intro m hm
        have hK : Even ({i, m} : Finset (Fin 6)).card := by
          rw [Finset.card_pair_eq_two_iff.mpr (Ne.symm hm)]
          exact even_two
        have hmem : σ i ∈ ({i, m} : Finset (Fin 6)).map σ.toEmbedding :=
          Finset.mem_map.mpr ⟨i, by simp, rfl⟩
        rw [hfix {i, m} hK] at hmem
        simpa using hmem
      rcases key m1 hm1 with h | h
      · exact h
      · rcases key m2 hm2 with h' | h'
        · exact h'
        · exact absurd (h.symm.trans h') hm12
    subst hσ1
    simp only [fr.permOrth_one, one_mul]
    have hJinv : ∀ ρ ∈ monoD, J.map ρ.toEmbedding = J := by
      intro ρ hρ
      have hcomm := hc (fr.permOrth ρ) (hp_mem ρ hρ)
      simp only [fr.permOrth_one, one_mul] at hcomm
      have hp := fr.permOrth_mul_signChange ρ J
      have : fr.signChange (J.map ρ.toEmbedding) * fr.permOrth ρ =
          fr.signChange J * fr.permOrth ρ := by
        rw [← hp]
        exact hcomm.symm
      exact fr.signChange_injective (mul_right_cancel this)
    rcases monoD_orbits hJinv with hJ | hJ | hJ | hJ
    · left; exact (congrArg fr.signChange hJ).trans fr.signChange_empty
    · right; left; exact congrArg fr.signChange hJ
    · right; right; left; exact congrArg fr.signChange hJ
    · right; right; right; exact congrArg fr.signChange hJ
  · rintro (rfl | rfl | rfl | rfl)
    · intro h _; simp
    · exact signChange_central_monoP (fr := fr) (P := P) hP (J := {0, 1, 2, 3})
        (fun ρ hρ => (monoD_map_orbit hρ).1)
    · exact signChange_central_monoP (fr := fr) (P := P) hP (J := {4, 5})
        (fun ρ hρ => (monoD_map_orbit hρ).2)
    · exact signChange_central_monoP (fr := fr) (P := P) hP (J := Finset.univ)
        (fun ρ hρ => Finset.map_univ_equiv ρ)

theorem t5_mono_cent {fr : NFrame Q (Fin 6) 1} {P : Subgroup (OGroup Q)}
    (hP : ∀ g, g ∈ P ↔ ∃ σ ∈ monoD, ∃ J : Finset (Fin 6), Even J.card ∧
      g = fr.permOrth σ * fr.signChange J)
    {x : simGroup Q} (hx : ∀ g ∈ P, simAct Q x g = g) :
    ∃ w : OGroup Q, (w = 1 ∨ w = fr.signChange {0, 1, 2, 3} ∨ w = fr.signChange {4, 5} ∨
      w = fr.signChange Finset.univ) ∧ x = orthToSim Q w := by
  set X : V ≃ₗ[ZMod 3] V := (x : V ≃ₗ[ZMod 3] V) with hX
  have ht_mem : ∀ K : Finset (Fin 6), Even K.card → fr.signChange K ∈ P := by
    intro K hK
    exact (hP _).mpr ⟨1, one_mem _, K, hK, by simp [fr.permOrth_one]⟩
  have hp_mem : ∀ ρ : Equiv.Perm (Fin 6), ρ ∈ monoD → fr.permOrth ρ ∈ P := by
    intro ρ hρ
    exact (hP _).mpr ⟨ρ, hρ, ∅, by decide, by simp [fr.signChange_empty]⟩
  have hXK : ∀ K : Finset (Fin 6), Even K.card →
      X * (fr.signChange K : V ≃ₗ[ZMod 3] V) =
        (fr.signChange K : V ≃ₗ[ZMod 3] V) * X := by
    intro K hK
    have h := hx (fr.signChange K) (ht_mem K hK)
    have h' := congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V)) h
    rw [coe_simAct] at h'
    rw [← hX] at h'
    calc X * (fr.signChange K : V ≃ₗ[ZMod 3] V)
        = (X * (fr.signChange K : V ≃ₗ[ZMod 3] V) * X⁻¹) * X := by group
      _ = (fr.signChange K : V ≃ₗ[ZMod 3] V) * X := by rw [h']
  have hcoord_zero : ∀ i m : Fin 6, m ≠ i → fr.b.repr (X (fr.b i)) m = 0 := by
    intro i m hm
    obtain ⟨k, hki, hkm⟩ := exists_ne_pair i m
    have hiK : i ∈ ({i, k} : Finset (Fin 6)) := by simp
    have hmK : m ∉ ({i, k} : Finset (Fin 6)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hm, fun h => hkm h.symm⟩
    have hK : Even ({i, k} : Finset (Fin 6)).card := by
      rw [Finset.card_pair_eq_two_iff.mpr hki.symm]
      exact even_two
    have happ := congrArg (fun f : V ≃ₗ[ZMod 3] V => f (fr.b i)) (hXK {i, k} hK)
    simp only [LinearEquiv.mul_apply] at happ
    rw [fr.signChange_basis ({i, k}) i, if_pos hiK, map_neg] at happ
    have hcoord := congrArg (fun v : V => fr.b.repr v m) happ
    rw [map_neg, Finsupp.neg_apply, fr.repr_signChange ({i, k}) (X (fr.b i)) m,
      if_neg hmK] at hcoord
    have h2 : (2 : ZMod 3) * fr.b.repr (X (fr.b i)) m = 0 := by
      rw [two_mul]
      exact eq_neg_iff_add_eq_zero.mp hcoord.symm
    exact (mul_eq_zero.mp h2).resolve_left (by decide)
  have hdiag : ∀ i, X (fr.b i) = fr.b.repr (X (fr.b i)) i • fr.b i := by
    intro i
    apply fr.b.ext_elem
    intro j
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self]
    by_cases hji : j = i
    · subst hji; simp
    · rw [Finsupp.single_eq_of_ne hji, mul_zero]
      exact hcoord_zero i j hji
  have hd_ne : ∀ i, fr.b.repr (X (fr.b i)) i ≠ 0 := by
    intro i h0
    have hzero : X (fr.b i) = 0 := by rw [hdiag i, h0, zero_smul]
    have : X (fr.b i) = X 0 := by rw [hzero, map_zero]
    exact fr.b.ne_zero i (X.injective this)
  have hd_pm : ∀ i, fr.b.repr (X (fr.b i)) i = 1 ∨ fr.b.repr (X (fr.b i)) i = -1 := by
    intro i
    have h : ∀ e : ZMod 3, e ≠ 0 → e = 1 ∨ e = -1 := by decide
    exact h _ (hd_ne i)
  obtain ⟨c, hc⟩ := x.2
  have hc_eq : c = 1 := by
    have h0 := hc (fr.b 0)
    rw [← hX] at h0
    rw [hdiag 0, fr.norm 0, mul_one] at h0
    have hsq : Q (fr.b.repr (X (fr.b 0)) 0 • fr.b 0) = 1 := by
      rw [QuadraticMap.map_smul, fr.norm 0, smul_eq_mul, mul_one]
      rcases hd_pm 0 with h | h <;> rw [h] <;> ring
    exact Units.ext (h0.symm.trans hsq)
  have hmem : X ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    apply isSimilitude_one_iff.mp
    rw [← hc_eq]
    exact hc
  set J : Finset (Fin 6) :=
    Finset.univ.filter (fun i => fr.b.repr (X (fr.b i)) i = -1) with hJdef
  have hXsign : X = (fr.signChange J : V ≃ₗ[ZMod 3] V) := by
    apply fr.b.ext'
    intro i
    rw [fr.signChange_basis J i, hdiag i]
    by_cases hi : i ∈ J
    · have hdi : fr.b.repr (X (fr.b i)) i = -1 := by
        rw [hJdef] at hi
        exact (Finset.mem_filter.mp hi).2
      rw [if_pos hi, hdi]; simp
    · rw [if_neg hi]
      rcases hd_pm i with h | h
      · rw [h]; simp
      · exfalso
        apply hi
        rw [hJdef]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩
  let w : OGroup Q := ⟨X, hmem⟩
  have hw_eq : w = fr.signChange J := Subtype.ext hXsign
  have hxw : x = orthToSim Q w := Subtype.ext (by rw [coe_orthToSim])
  have hJinv : ∀ ρ ∈ monoD, J.map ρ.toEmbedding = J := by
    intro ρ hρ
    have hcomm := hx (fr.permOrth ρ) (hp_mem ρ hρ)
    rw [hxw, simAct_orthToSim] at hcomm
    have hwcomm : w * fr.permOrth ρ = fr.permOrth ρ * w := by
      calc w * fr.permOrth ρ = (w * fr.permOrth ρ * w⁻¹) * w := by group
        _ = fr.permOrth ρ * w := by rw [hcomm]
    have hcommJ : fr.signChange J * fr.permOrth ρ =
        fr.permOrth ρ * fr.signChange J := by
      rw [← hw_eq]
      exact hwcomm
    have hp := fr.permOrth_mul_signChange ρ J
    have : fr.signChange (J.map ρ.toEmbedding) * fr.permOrth ρ =
        fr.signChange J * fr.permOrth ρ := by
      rw [← hp]
      exact hcommJ.symm
    exact fr.signChange_injective (mul_right_cancel this)
  refine ⟨w, ?_, hxw⟩
  rcases monoD_orbits hJinv with hJ | hJ | hJ | hJ
  · left; exact hw_eq.trans ((congrArg fr.signChange hJ).trans fr.signChange_empty)
  · right; left; exact hw_eq.trans (congrArg fr.signChange hJ)
  · right; right; left; exact hw_eq.trans (congrArg fr.signChange hJ)
  · right; right; right; exact hw_eq.trans (congrArg fr.signChange hJ)

theorem t5_f53_model (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hs : quadSign Q = -1) :
    ∃ (P₀ : Subgroup (OGroup Q)) (z₀ : OGroup Q), P₀ ≤ omegaGroup hQ ∧ Nat.card P₀ = 2 ^ 8 ∧
      z₀ ∈ P₀ ∧ piOrth Q ∈ P₀ ∧ invType z₀ = (4, 1) ∧
      (∀ g ∈ P₀, (∀ h ∈ P₀, g * h = h * g) ↔
        (g = 1 ∨ g = z₀ ∨ g = piOrth Q * z₀ ∨ g = piOrth Q)) ∧
      ∀ x : simGroup Q, (∀ g ∈ P₀, simAct Q x g = g) →
        ∃ w : OGroup Q, (w = 1 ∨ w = z₀ ∨ w = piOrth Q * z₀ ∨ w = piOrth Q) ∧
          x = orthToSim Q w := by
  obtain ⟨fr⟩ := exists_nframe_six hQ hdim hs
  obtain ⟨P, hPle, hPcard, hP⟩ := t5_exists_monoP hQ fr
  set z₀ : OGroup Q := fr.signChange {0, 1, 2, 3} with hz₀
  have hpi : piOrth Q = fr.signChange Finset.univ := fr.piOrth_eq_signChange_univ
  have hprod : piOrth Q * z₀ = fr.signChange {4, 5} := by
    rw [hz₀, hpi, fr.signChange_mul]
    congr 1
  have hzP : z₀ ∈ P := by
    rw [hP z₀]
    exact ⟨1, one_mem _, {0, 1, 2, 3}, by decide, by simp [hz₀, fr.permOrth_one]⟩
  have hpiP : piOrth Q ∈ P := by
    rw [hpi, hP (fr.signChange Finset.univ)]
    exact ⟨1, one_mem _, Finset.univ, by decide, by simp [fr.permOrth_one]⟩
  have hztype : invType z₀ = (4, 1) := by
    rw [hz₀, fr.invType_signChange hQ {0, 1, 2, 3} (by decide)]
    decide
  refine ⟨P, z₀, hPle, hPcard, hzP, hpiP, hztype, ?_, ?_⟩
  · intro g hg
    rw [t5_mono_center (fr := fr) (P := P) hP hg]
    simp only [← hprod, ← hz₀, ← hpi]
  · intro x hx
    obtain ⟨w, hw, hxw⟩ := t5_mono_cent (fr := fr) (P := P) hP hx
    exact ⟨w, by simpa only [← hprod, ← hz₀, ← hpi] using hw, hxw⟩

end CFSG.OddStandard.SmallF3.Omega
