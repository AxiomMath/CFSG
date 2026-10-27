module

public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusAct
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusNum

public section

namespace CFSG.ClassicalInvolution.ModelFacts.ChevAut

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

section Diag

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}

@[expose] def diagChar (b : Fin D.rank → Fˣ) (γ : Fin D.rank → ℤ) : Fˣ := ∏ i, b i ^ γ i

theorem diagChar_single (b : Fin D.rank → Fˣ) (i : Fin D.rank) :
    diagChar b (Pi.single i 1) = b i := by
  rw [diagChar, Finset.prod_eq_single i]
  · simp
  · intro l _ hl
    simp [hl]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem diagChar_neg (b : Fin D.rank → Fˣ) (γ : Fin D.rank → ℤ) :
    diagChar b (-γ) = (diagChar b γ)⁻¹ := by
  simp [diagChar, zpow_neg, Finset.prod_inv_distrib]

theorem diagChar_reflection (b : Fin D.rank → Fˣ) (i : Fin D.rank) (γ : Fin D.rank → ℤ) :
    diagChar b (reflection D.cartan i γ) = diagChar b γ * b i ^ (-pair D.cartan γ i) := by
  have h : ∀ l, b l ^ (reflection D.cartan i γ) l =
      b l ^ γ l * (Pi.mulSingle i (b i ^ (-pair D.cartan γ i)) : Fin D.rank → Fˣ) l := by
    intro l
    rw [reflection_apply]
    by_cases hl : l = i
    · subst hl
      simp [pair, sub_eq_add_neg, zpow_add, zpow_neg]
    · simp [hl]
  rw [diagChar, Finset.prod_congr rfl fun l _ => h l, Finset.prod_mul_distrib,
    Finset.prod_pi_mulSingle']
  simp [diagChar]


variable {α : K →* K} {g : K} {a : Fin D.rank → Fˣ} {φ : F ≃+* F} {π : Equiv.Perm (Fin D.rank)}

theorem alpha_weylElement
    (hα₁ : ∀ i c, α (x (Pi.single i 1) c) =
      g * x (Pi.single (π i) 1) ((a (π i) : F) * φ c) * g⁻¹)
    (hα₂ : ∀ i c, α (x (-Pi.single i 1) c) =
      g * x (-Pi.single (π i) 1) ((((a (π i))⁻¹ : Fˣ) : F) * φ c) * g⁻¹)
    (i : Fin D.rank) (t : Fˣ) :
    α (weylElement x i t) =
      g * weylElement x (π i) (a (π i) * Units.map (φ : F →+* F) t) * g⁻¹ := by
  unfold weylElement
  rw [map_mul, map_mul, hα₁, hα₂]
  have e1 : (a (π i) : F) * φ (t : F) =
      ((a (π i) * Units.map (φ : F →+* F) t : Fˣ) : F) := by simp
  have e2 : (((a (π i))⁻¹ : Fˣ) : F) * φ (-((t⁻¹ : Fˣ) : F)) =
      -(((a (π i) * Units.map (φ : F →+* F) t)⁻¹ : Fˣ) : F) := by
    simp only [map_neg]
    simp
    exact mul_comm _ _
  rw [e1, e2]
  group

theorem alpha_torusGen
    (hom : ∀ i s s', torusGen x i (s * s') = torusGen x i s * torusGen x i s')
    (hα₁ : ∀ i c, α (x (Pi.single i 1) c) =
      g * x (Pi.single (π i) 1) ((a (π i) : F) * φ c) * g⁻¹)
    (hα₂ : ∀ i c, α (x (-Pi.single i 1) c) =
      g * x (-Pi.single (π i) 1) ((((a (π i))⁻¹ : Fˣ) : F) * φ c) * g⁻¹)
    (i : Fin D.rank) (s : Fˣ) :
    α (torusGen x i s) = g * torusGen x (π i) (Units.map (φ : F →+* F) s) * g⁻¹ := by
  have hw : ∀ (j : Fin D.rank) (u : Fˣ), weylElement x j u = torusGen x j u * weylElement x j 1 :=
    fun j u => by simp [torusGen]
  unfold torusGen
  rw [map_mul, map_inv, alpha_weylElement hα₁ hα₂, alpha_weylElement hα₁ hα₂, map_one]
  set u := a (π i) with hu
  set v : Fˣ := Units.map (φ : F →+* F) s with hv
  rw [hw (π i) (u * v), hw (π i) (u * 1)]
  have h1 : torusGen x (π i) (u * v) = torusGen x (π i) v * torusGen x (π i) u := by
    rw [mul_comm u v, hom]
  rw [mul_one, h1]
  simp only [torusGen]
  group


structure NormalForm (x : (Fin D.rank → ℤ) → F → K) (α : K →* K) (g : K)
    (a : Fin D.rank → Fˣ) (φ : F ≃+* F) (π : Equiv.Perm (Fin D.rank)) : Prop where
  pos : ∀ i c, α (x (Pi.single i 1) c) = g * x (Pi.single (π i) 1) ((a (π i) : F) * φ c) * g⁻¹
  neg : ∀ i c, α (x (-Pi.single i 1) c) =
    g * x (-Pi.single (π i) 1) ((((a (π i))⁻¹ : Fˣ) : F) * φ c) * g⁻¹

variable {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

theorem conj_mem_iSup_of_alpha (hS : TorusSetup D x n H) (hN : NormalForm x α g a φ π)
    (hfix : ∀ i s, α (torusGen x i s) * (torusGen x i s)⁻¹ ∈ Subgroup.center K) :
    ∀ t ∈ ⨆ i, H i, g * t * g⁻¹ ∈ ⨆ i, H i := by
  have hgen : ∀ i' s', g * torusGen x i' s' * g⁻¹ ∈ ⨆ i, H i := by
    intro i' s'
    have h1 := alpha_torusGen hS.hom hN.pos hN.neg (π.symm i')
      (Units.map (φ.symm : F →+* F) s')
    rw [Equiv.apply_symm_apply] at h1
    have h2 : (Units.map (φ : F →+* F) (Units.map (φ.symm : F →+* F) s' : Fˣ) : Fˣ) = s' := by
      ext; simp
    rw [h2] at h1
    rw [← h1]
    have h3 := mul_mem (hS.center_le (hfix (π.symm i') (Units.map (φ.symm : F →+* F) s')))
      (hS.torusGen_mem (π.symm i') (Units.map (φ.symm : F →+* F) s'))
    rwa [inv_mul_cancel_right] at h3
  intro t ht
  have hle : (⨆ i, H i) ≤ (⨆ i, H i).comap (MulAut.conj g).toMonoidHom := by
    refine iSup_le fun i y hy => ?_
    obtain ⟨s, rfl⟩ := (hS.H_iff i y).1 hy
    exact hgen i s
  exact hle ht

theorem char_eq_of_alpha (hS : TorusSetup D x n H) (hN : NormalForm x α g a φ π)
    (hfix : ∀ i s, α (torusGen x i s) * (torusGen x i s)⁻¹ ∈ Subgroup.center K)
    {h : K} (hh : h ∈ ⨆ i, H i) {w : (coxeterMatrix D.isFiniteType).Group}
    (hg : g = h * nrep hS.ct w) (j : Fin D.rank) (s : Fˣ) {δ : Fin D.rank → ℤ}
    (hδ : δ ∈ D.roots) :
    Units.map (φ : F →+* F) s ^ pair D.cartan δ (π j) =
      s ^ pair D.cartan (weylAction D.isFiniteType w δ) j := by
  obtain ⟨C, O, hE⟩ := hS.chev
  have hδ' : weylAction D.isFiniteType w δ ∈ D.roots := weylAction_mem_roots D.isFiniteType w hδ
  have h1 := torusGen_act hE hδ (π j) (Units.map (φ : F →+* F) s)
  obtain ⟨ε, hε, hεc⟩ := signConj_nrep hE hS.ct hS.n_eq w δ hδ
  have h2 := TAct.conj_of_sign hε hεc h1
  obtain ⟨lam, hlam⟩ := exists_tact_of_mem_iSup hE hS.H_iff hh
  have h3 := TAct.conj (hlam _ hδ') h2
  have h4 : g * torusGen x (π j) (Units.map (φ : F →+* F) s) * g⁻¹ =
      h * (nrep hS.ct w * torusGen x (π j) (Units.map (φ : F →+* F) s) * (nrep hS.ct w)⁻¹) *
        h⁻¹ := by
    rw [hg]; group
  have h5 := alpha_torusGen hS.hom hN.pos hN.neg j s
  have h6 : α (torusGen x j s) =
      (α (torusGen x j s) * (torusGen x j s)⁻¹) * torusGen x j s := by group
  have h7 : TAct x (α (torusGen x j s)) (weylAction D.isFiniteType w δ)
      (s ^ pair D.cartan (weylAction D.isFiniteType w δ) j) := by
    rw [h6]
    exact TAct.central_mul (hfix j s) (torusGen_act hE hδ' j s)
  rw [h5, h4] at h7
  exact TAct.unique (hE.param _ hδ').2.2 h3 h7


theorem roots_empty (hS : TorusSetup D x n H) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    γ ∈ roots D.isFiniteType ∅ := by
  rw [← hS.div]
  exact hγ

theorem eq_one_of_char_eq [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hS : TorusSetup D x n H) (hp2 : p ≠ 2) (hq : 5 ≤ Nat.card F) (hr : 0 < D.rank)
    (hlong : ∀ k, IsLongest D.isFiniteType ∅ (Pi.single k 1))
    (hnb : ∀ k, ∃ j, D.cartan j k = -1)
    (hAij : ∀ i j, i ≠ j → D.cartan i j = 0 ∨ D.cartan i j = -1)
    (hπ : ∀ j l, D.cartan (π j) (π l) = D.cartan j l) {w : (coxeterMatrix D.isFiniteType).Group}
    (hchar : ∀ (j : Fin D.rank) (s : Fˣ) (δ : Fin D.rank → ℤ), δ ∈ D.roots →
      Units.map (φ : F →+* F) s ^ pair D.cartan δ (π j) =
        s ^ pair D.cartan (weylAction D.isFiniteType w δ) j) :
    φ = 1 ∧ w = 1 ∧ π = 1 := by
  have step : ∀ k : Fin D.rank, φ = 1 ∧
      weylAction D.isFiniteType w (Pi.single k 1) = Pi.single (π.symm k) 1 := by
    intro k
    have hk : (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots :=
      (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k
    have hγ : weylAction D.isFiniteType w (Pi.single k 1) ∈ D.roots :=
      weylAction_mem_roots D.isFiniteType w hk
    have hγ' := roots_empty hS hγ
    obtain ⟨j', hj'⟩ := hnb k
    obtain ⟨hφ, hcd, hc2⟩ := frob_cong hp2 hq φ (fun j => D.cartan (π j) k)
      (fun j => pair D.cartan (weylAction D.isFiniteType w (Pi.single k 1)) j) (π.symm k)
      (π.symm j') (fun j => abs_pair_le D.isFiniteType hlong hγ' j)
      (by simp [D.isFiniteType.apply_self])
      (fun j hj => hAij (π j) k (fun h => hj (by rw [← h]; simp)))
      (by simp [hj'])
      (fun s j => by
        have := hchar j s (Pi.single k 1) hk
        rwa [pair_single] at this)
    refine ⟨hφ, ?_⟩
    have hpair_single : ∀ j, pair D.cartan (Pi.single (π.symm k) 1) j = D.cartan (π j) k := by
      intro j
      rw [pair_single, ← hπ j (π.symm k), Equiv.apply_symm_apply]
    rcases hc2 with h2 | h2
    · have hz : ∀ j, pair D.cartan (weylAction D.isFiniteType w (Pi.single k 1) -
          Pi.single (π.symm k) 1) j = 0 := by
        intro j
        rw [pair_sub, hpair_single]
        by_cases hj : j = π.symm k
        · subst hj
          rw [h2]
          simp [D.isFiniteType.apply_self]
        · rw [hcd j hj]
          ring
      exact sub_eq_zero.1 (eq_zero_of_pair_eq_zero D.isFiniteType hz)
    · exfalso
      have hneg := eq_neg_single_of_pair_eq_neg_two D.isFiniteType hlong hγ' h2
      obtain ⟨j'', hj''⟩ := hnb (π.symm k)
      have hne : j'' ≠ π.symm k := fun h => by
        rw [h, D.isFiniteType.apply_self] at hj''
        omega
      have h3 := hcd j'' hne
      have h4 : D.cartan (π j'') k = -1 := by
        rw [← hj'', ← hπ j'' (π.symm k), Equiv.apply_symm_apply]
      rw [hneg, pair_neg, pair_single, hj''] at h3
      omega
  have hw1 : w = 1 := by
    by_contra hw
    obtain ⟨i, hi⟩ :=
      (coxeterMatrix D.isFiniteType).toCoxeterSystem.exists_rightDescent_of_ne_one hw
    have h1 := ht_weylAction_single_neg (D := D) hi
    rw [(step i).2] at h1
    have h2 := ht_single_pos (D := D) (π.symm i)
    omega
  refine ⟨(step ⟨0, hr⟩).1, hw1, Equiv.ext fun k => ?_⟩
  have h1 := (step k).2
  rw [hw1, map_one, Module.End.one_apply] at h1
  have h2 : π.symm k = k := by
    by_contra hne
    have := congrFun h1 k
    simp [hne] at this
  have h3 := congrArg π h2
  rw [Equiv.apply_symm_apply] at h3
  simpa using h3.symm


theorem exists_diag_of_fixes_torus [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hS : TorusSetup D x n H) (hp2 : p ≠ 2) (hq : 5 ≤ Nat.card F) (hr : 0 < D.rank)
    (hlong : ∀ k, IsLongest D.isFiniteType ∅ (Pi.single k 1))
    (hnb : ∀ k, ∃ j, D.cartan j k = -1)
    (hAij : ∀ i j, i ≠ j → D.cartan i j = 0 ∨ D.cartan i j = -1)
    (hπ : ∀ j l, D.cartan (π j) (π l) = D.cartan j l) (hN : NormalForm x α g a φ π)
    (hfix : ∀ i s, α (torusGen x i s) * (torusGen x i s)⁻¹ ∈ Subgroup.center K) :
    ∃ b : Fin D.rank → Fˣ, ∀ γ ∈ D.roots, ∀ c, α (x γ c) = x γ ((diagChar b γ : F) * c) := by
  obtain ⟨C, O, hE⟩ := hS.chev
  have hno := hS.hno hp2 hlong hnb
  obtain ⟨h, hh, w, hg⟩ := exists_mem_iSup_mul_nrep_of_forall_conj_mem hS.ct hS.ext hS.bru hno
    (conj_mem_iSup_of_alpha hS hN hfix)
  obtain ⟨hφ, hw, hπ1⟩ := eq_one_of_char_eq hS hp2 hq hr hlong hnb hAij hπ
    (fun j s δ hδ => char_eq_of_alpha hS hN hfix hh hg j s hδ)
  subst hw hπ1 hφ
  rw [nrep_one, mul_one] at hg
  subst hg
  obtain ⟨lam, hlam⟩ := exists_tact_of_mem_iSup hE hS.H_iff hh
  set b : Fin D.rank → Fˣ := fun i => charVal D.cartan lam (Pi.single i 1) * a i with hb
  have hroot : ∀ i, (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := fun i =>
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hsimple₁ : ∀ i c, α (x (Pi.single i 1) c) = x (Pi.single i 1) ((b i : F) * c) := by
    intro i c
    rw [hN.pos i c]
    simp only [Equiv.Perm.coe_one, id_eq]
    rw [show (1 : F ≃+* F) c = c from rfl, hlam _ (hroot i)]
    congr 1
    simp [hb]
    ring
  have hsimple₂ : ∀ i c, α (x (-Pi.single i 1) c) =
      x (-Pi.single i 1) ((((b i)⁻¹ : Fˣ) : F) * c) := by
    intro i c
    rw [hN.neg i c]
    simp only [Equiv.Perm.coe_one, id_eq]
    rw [show (1 : F ≃+* F) c = c from rfl,
      hlam _ (CFSG.LieType.Steinberg.OfCartan.neg_mem_roots D.isFiniteType (hroot i)),
      charVal_neg]
    congr 1
    simp [hb]
    ring
  have hbase : ∀ k c, α (x (Pi.single k 1) c) =
      x (Pi.single k 1) ((diagChar b (Pi.single k 1) : F) * c) := by
    intro k c
    rw [diagChar_single]
    exact hsimple₁ k c
  have hw1 : ∀ i, α (weylElement x i 1) = weylElement x i (b i) := by
    intro i
    unfold weylElement
    rw [map_mul, map_mul, hsimple₁ i, hsimple₂ i]
    simp
  have hstep : ∀ (i : Fin D.rank) (δ : Fin D.rank → ℤ), δ ∈ D.roots →
      (∀ c, α (x δ c) = x δ ((diagChar b δ : F) * c)) →
      ∀ c, α (x (reflection D.cartan i δ) c) =
        x (reflection D.cartan i δ) ((diagChar b (reflection D.cartan i δ) : F) * c) := by
    intro i δ hδ hR c
    obtain ⟨ε, hε, hεw⟩ := hE.weyl i δ hδ
    have hε2 : (ε : F) * ε = 1 := by rcases hε with rfl | rfl <;> simp
    have h1 : x (reflection D.cartan i δ) c =
        weylElement x i 1 * x δ ((ε : F) * c) * (weylElement x i 1)⁻¹ := by
      rw [hεw 1 ((ε : F) * c)]
      congr 1
      simp
      linear_combination (-c) * hε2
    rw [h1, map_mul, map_mul, hR, hw1, map_inv, hw1, hεw (b i)]
    congr 1
    rw [diagChar_reflection]
    simp only [Units.val_mul, pair]
    linear_combination ((diagChar b δ : F) * ((b i ^ (-∑ l, D.cartan i l * δ l) : Fˣ) : F) * c)
      * hε2
  refine ⟨b, fun γ hγ => ?_⟩
  have key : ∀ (k : Fin D.rank) (ω : List (Fin D.rank)), ∀ c,
      α (x (weylAction D.isFiniteType
        ((coxeterMatrix D.isFiniteType).toCoxeterSystem.wordProd ω) (Pi.single k 1)) c) =
      x (weylAction D.isFiniteType
        ((coxeterMatrix D.isFiniteType).toCoxeterSystem.wordProd ω) (Pi.single k 1))
        ((diagChar b (weylAction D.isFiniteType
          ((coxeterMatrix D.isFiniteType).toCoxeterSystem.wordProd ω) (Pi.single k 1)) : F) *
          c) := by
    intro k ω
    induction ω with
    | nil => simpa using hbase k
    | cons i ω ih =>
      rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, weylAction_simple]
      exact hstep i _ (weylAction_mem_roots D.isFiniteType _ (hroot k)) ih
  have hγ0 : γ ∈ roots D.isFiniteType D.divisible := hγ
  rcases hγ0 with ⟨w, k, rfl⟩ | ⟨w, k, hk, rfl⟩
  · obtain ⟨ω, -, rfl⟩ := (coxeterMatrix D.isFiniteType).toCoxeterSystem.exists_isReduced w
    exact key k ω
  · rw [hS.div] at hk
    exact absurd hk (Set.notMem_empty _)

end Diag

end CFSG.ClassicalInvolution.ModelFacts.ChevAut
