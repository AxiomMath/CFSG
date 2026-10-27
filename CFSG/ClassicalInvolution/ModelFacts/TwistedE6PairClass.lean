module

public import CFSG.ClassicalInvolution.ModelFacts.TwistedE6PairCommute
public import CFSG.ClassicalInvolution.ModelFacts.TwistedE6PairLevi
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Sign
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLeviToral

public section

namespace CFSG.ClassicalInvolution.ModelFacts.LeviE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.Levi

section Sign

@[expose] def e6SignChar (δ : Fin (Tag.rank .E6) → ℤ) :
    Multiplicative (Fin (Tag.rank .E6) → ℤ) →* ℤˣ where
  toFun v := (-1 : ℤˣ) ^ iform δ (Multiplicative.toAdd v)
  map_one' := by
    have : iform δ (0 : Fin (Tag.rank .E6) → ℤ) = 0 := by simp [iform]
    simp [this]
  map_mul' u v := by
    rw [toAdd_mul, iform_add_right, zpow_add]

theorem signCharTuple_e6SignChar {k : Type} [Field k] (δ : Fin (Tag.rank .E6) → ℤ) :
    signCharTuple (k := k) (e6SignChar δ) = thetaDiag δ (-1 : kˣ) := by
  funext i
  have h : intUnitsMap k (-1 : ℤˣ) = -1 := Units.ext (by simp [intUnitsMap])
  simp only [signCharTuple, e6SignChar, thetaDiag, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
    map_zpow, h]

theorem thetaDiag_neg_E6 {k : Type} [Field k] (δ : Fin (Tag.rank .E6) → ℤ) :
    thetaDiag (-δ) (-1 : kˣ) = thetaDiag δ (-1 : kˣ) := by
  funext i
  have h1 : iform (-δ) (Pi.single i 1) = -iform δ (Pi.single i 1) := by
    rw [show (-δ : Fin (Tag.rank .E6) → ℤ) = (-1 : ℤ) • δ by simp, iform_smul_left]
    ring
  simp only [thetaDiag, h1]
  rcases Int.even_or_odd (iform δ (Pi.single i 1)) with he | ho
  · rw [he.neg_one_zpow, (he.neg).neg_one_zpow]
  · rw [ho.neg_one_zpow, (ho.neg).neg_one_zpow]

end Sign

section Class

variable {k : Type} [Field k] [IsAlgClosed k]

theorem exists_root_of_conj_thetaDiag_E6 (hk : ringChar k ≠ 2) {a : Fin (Tag.rank .E6) → kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) {g : ModGL .E6 k} (hg : g ∈ adjointGroup .E6 k)
    (hga : g * rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : kˣ)) * g⁻¹ = rootDiagUnit .E6 a) :
    ∃ δ, IsRoot .E6 δ ∧ a = thetaDiag δ (-1 : kˣ) := by
  have ha' := eq_signCharTuple_of_sign hk ha
  rw [← signCharTuple_e6SignChar thetaE6 (k := k)] at hga
  rw [ha'] at hga
  obtain ⟨t, ht⟩ := (exists_conj_rootDiagUnit_signCharTuple_iff hk (e6SignChar thetaE6)
    (maskChar (signTupleBits a))).1 ⟨g, hg, hga⟩
  refine ⟨t • thetaE6, IsRoot.smul isRoot_thetaE6 t, ?_⟩
  rw [ha']
  funext i
  rw [← signCharTuple_e6SignChar (t • thetaE6) (k := k)]
  simp only [signCharTuple]
  congr 1
  rw [ht (Pi.single i 1)]
  simp only [e6SignChar, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  have := iform_smul_smul t thetaE6 (t⁻¹ • (Pi.single i 1 : Fin (Tag.rank .E6) → ℤ))
  rw [smul_inv_smul] at this
  rw [this]

theorem uSL_injective_E6 {F : Type} [Field F] : Function.Injective (uSL : F → SL2 F) :=
  fun a b h => by
    have := congrArg (fun M : SL2 F => (M : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simpa [uSL] using this

end Class

section Alpha4

@[expose] def alpha4E6 : Fin (Tag.rank .E6) → ℤ := Pi.single ⟨3, by decide⟩ 1

theorem isRoot_alpha4E6 : IsRoot .E6 alpha4E6 := isRoot_single .E6 _

theorem iform_thetaE6_alpha4E6 : iform thetaE6 alpha4E6 = 0 := by
  rw [iform_thetaE6_eq]
  simp [alpha4E6]

theorem perm_alpha4E6 : permLattice TwistTag.E6.perm alpha4E6 = alpha4E6 :=
  List.ofFn_injective (by decide : List.ofFn (permLattice TwistTag.E6.perm alpha4E6) =
    List.ofFn alpha4E6)

theorem iform_alpha4E6_single (i : Fin (Tag.rank .E6)) :
    iform alpha4E6 (Pi.single i 1) =
      if i.val = 1 ∨ i.val = 2 ∨ i.val = 4 then -1 else if i.val = 3 then 2 else 0 := by
  fin_cases i <;> decide

abbrev toIdx (j : Fin 6) : Fin (Tag.rank .E6) := j

def applyRefl (l : List (Fin 6)) (v : Fin (Tag.rank .E6) → ℤ) : Fin (Tag.rank .E6) → ℤ :=
  l.foldr (fun j u => reflect Tag.E6 (toIdx j) u) v

def wordWeyl (l : List (Fin 6)) : WeylGroup .E6 := (l.map fun j => simple .E6 (toIdx j)).prod

theorem wordWeyl_smul (l : List (Fin 6)) (v : Fin (Tag.rank .E6) → ℤ) :
    wordWeyl l • v = applyRefl l v := by
  induction l with
  | nil => simp [wordWeyl, applyRefl]
  | cons j l ih =>
    have e : wordWeyl (j :: l) = simple .E6 (toIdx j) * wordWeyl l := by
      simp [wordWeyl]
    rw [e, mul_smul, ih, simple_smul]
    rfl

@[expose] def alpha4OrbitWords : List (List (Fin 6)) :=
  [[], [2], [3], [4], [0, 2], [2, 3], [3, 2], [3, 4], [4, 2], [4, 3], [5, 4], [0, 2, 3],
    [2, 3, 2], [3, 0, 2], [3, 4, 3], [4, 0, 2], [4, 2, 3], [5, 3, 4], [5, 4, 2], [5, 4, 3],
    [0, 2, 3, 2], [2, 3, 0, 2], [4, 0, 2, 3], [4, 5, 3, 4], [5, 3, 4, 3], [5, 4, 0, 2],
    [5, 4, 2, 3], [0, 2, 3, 0, 2], [4, 5, 3, 4, 3], [5, 4, 0, 2, 3]]

theorem exists_alpha4OrbitWord {δ : Fin (Tag.rank .E6) → ℤ} (hδ : IsRoot .E6 δ)
    (h0 : iform thetaE6 δ = 0) :
    ∃ l ∈ alpha4OrbitWords, (∀ j ∈ l, j ≠ (1 : Fin 6)) ∧ applyRefl l alpha4E6 = δ := by
  have h : ∀ δ ∈ rootFinset .E6, iform thetaE6 δ = 0 →
      ∃ l ∈ alpha4OrbitWords, (∀ j ∈ l, j ≠ (1 : Fin 6)) ∧ applyRefl l alpha4E6 = δ := by
    decide +kernel
  exact h δ (mem_rootFinset.2 hδ) h0

theorem exists_mem_parabolicWeylGroup_smul_alpha4 {δ : Fin (Tag.rank .E6) → ℤ}
    (hδ : IsRoot .E6 δ) (h0 : iform thetaE6 δ = 0) :
    ∃ w ∈ parabolicWeylGroup .E6 JE6, w • alpha4E6 = δ := by
  obtain ⟨l, -, hl, hδl⟩ := exists_alpha4OrbitWord hδ h0
  refine ⟨wordWeyl l, ?_, by rw [wordWeyl_smul, hδl]⟩
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  have hj1 : (toIdx j).val ≠ 1 := fun h => hl j hj (Fin.ext (by simpa using h))
  exact Subgroup.subset_closure ⟨toIdx j, hj1, rfl⟩

theorem weylTuple_thetaDiag {k : Type} [Field k] (w : WeylGroup .E6)
    (δ : Fin (Tag.rank .E6) → ℤ) (c : kˣ) :
    weylTuple w (thetaDiag δ c) = thetaDiag (w • δ) c := by
  funext i
  simp only [weylTuple, rootChar_thetaDiag, thetaDiag]
  congr 1
  rw [← iform_smul_smul w δ (w⁻¹ • (Pi.single i 1 : Fin (Tag.rank .E6) → ℤ)), smul_inv_smul]

theorem exists_levi_conj_thetaDiag_alpha4 {k : Type} [Field k] {δ : Fin (Tag.rank .E6) → ℤ}
    (hδ : IsRoot .E6 δ) (h0 : iform thetaE6 δ = 0) :
    ∃ n ∈ parabolicLevi .E6 k JE6, n * rootDiagUnit .E6 (thetaDiag δ (-1 : kˣ)) * n⁻¹ =
      rootDiagUnit .E6 (thetaDiag alpha4E6 (-1 : kˣ)) := by
  obtain ⟨w, hw, hwδ⟩ := exists_mem_parabolicWeylGroup_smul_alpha4 hδ h0
  refine ⟨canonicalRep (coxeterSystem .E6) k w⁻¹, canonicalRep_mem_parabolicLevi (inv_mem hw), ?_⟩
  rw [canonicalRep_conj_rootDiagUnit, weylTuple_thetaDiag, ← hwδ, inv_smul_smul]

variable {k : Type} [Field k]

theorem rootDiagUnit_thetaDiag_mem_sign_of_parity (δ : Fin (Tag.rank .E6) → ℤ)
    (m : Fin (Tag.rank .F4) → ℤ)
    (h : ∀ i, Even (iform δ (Pi.single i 1) -
      m (CFSG.LieType.Steinberg.TwistedE6.orbitMap i))) :
    rootDiagUnit TwistTag.E6.tag (thetaDiag δ (-1 : kˣ)) ∈ e6SignDiagonalGroup k := by
  refine ⟨fun j => (-1 : kˣ) ^ m j, fun j => ?_, congrArg (rootDiagUnit TwistTag.E6.tag) ?_⟩
  · rcases Int.even_or_odd (m j) with hm | hm
    · exact Or.inl hm.neg_one_zpow
    · exact Or.inr hm.neg_one_zpow
  · have key : ∀ i : Fin (Tag.rank .E6), (-1 : kˣ) ^ iform δ (Pi.single i 1) =
        (-1 : kˣ) ^ m (CFSG.LieType.Steinberg.TwistedE6.orbitMap i) := by
      intro i
      obtain ⟨r, hr⟩ := h i
      have he : Even (r + r) := ⟨r, rfl⟩
      rw [show iform δ (Pi.single i 1) = m (CFSG.LieType.Steinberg.TwistedE6.orbitMap i) + (r + r)
        by omega, zpow_add, he.neg_one_zpow, mul_one]
    funext i
    exact key i

theorem rootDiagUnit_thetaDiag_thetaE6_mem_sign :
    rootDiagUnit TwistTag.E6.tag (thetaDiag thetaE6 (-1 : kˣ)) ∈ e6SignDiagonalGroup k :=
  rootDiagUnit_thetaDiag_mem_sign_of_parity thetaE6 ![1, 0, 0, 0] (by
    intro i
    simp only [iform_thetaE6_single_eq]
    fin_cases i <;> decide)

theorem rootDiagUnit_thetaDiag_alpha4E6_mem_sign :
    rootDiagUnit TwistTag.E6.tag (thetaDiag alpha4E6 (-1 : kˣ)) ∈ e6SignDiagonalGroup k :=
  rootDiagUnit_thetaDiag_mem_sign_of_parity alpha4E6 ![1, 0, 1, 0] (by
    intro i
    simp only [iform_alpha4E6_single]
    fin_cases i <;> decide)

end Alpha4

section Glue

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem exists_levi_fixed_conj_or_eq_thetaDiag_E6
    (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) (hp2 : p ≠ 2) {e : ℕ}
    (he : 1 ≤ e) {y g : ModGL .E6 k}
    (hy : y ∈ parabolicLevi .E6 k JE6) (hy2 : y ^ 2 = 1)
    (hFy : frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) y = y)
    (hg : g ∈ adjointGroup .E6 k)
    (hgy : g * rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : kˣ)) * g⁻¹ = y)
    (hyU : y * rootSL2 .E6 k thetaE6 (uSL 1) = rootSL2 .E6 k thetaE6 (uSL 1) * y) :
    y = rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : kˣ)) ∨
      ∃ h ∈ parabolicLevi .E6 k JE6,
        frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) h = h ∧
          h * y * h⁻¹ = rootDiagUnit .E6 (thetaDiag alpha4E6 (-1 : kˣ)) := by
  have hk : ringChar k ≠ 2 := by rw [ringChar.eq k p]; exact hp2
  obtain ⟨v, hv, a, ha, hva⟩ := exists_levi_conj_eq_rootDiagUnit (τ := .E6) hp2 k halg hy hy2
  have hvg : v * g ∈ adjointGroup .E6 k :=
    mul_mem (parabolicSubgroup_le_adjointGroup _ _ _ (parabolicLevi_le_parabolicSubgroup JE6 hv)) hg
  obtain ⟨δ, hδ, rfl⟩ := exists_root_of_conj_thetaDiag_E6 hk ha hvg
    (by rw [← hva, ← hgy]; group)
  obtain ⟨l, hu, -⟩ := exists_levi_conj_rootSL2_thetaE6 hv
  have hinj : Function.Injective (rootSL2 .E6 k thetaE6) :=
    ((exceptional_Lang_root_rank_one_data .E6 k thetaE6).2.2.2.2.2.2.2.1 hk).1
  have hχ : rootChar (thetaDiag δ (-1 : kˣ)) thetaE6 = 1 := by
    have h1 : rootDiagUnit .E6 (thetaDiag δ (-1 : kˣ)) *
          rootSL2 .E6 k thetaE6 (uSL ((l : k) * 1)) =
        rootSL2 .E6 k thetaE6 (uSL ((l : k) * 1)) * rootDiagUnit .E6 (thetaDiag δ (-1 : kˣ)) := by
      rw [← hu 1, ← hva]
      calc v * y * v⁻¹ * (v * rootSL2 .E6 k thetaE6 (uSL 1) * v⁻¹) =
          v * (y * rootSL2 .E6 k thetaE6 (uSL 1)) * v⁻¹ := by group
        _ = v * (rootSL2 .E6 k thetaE6 (uSL 1) * y) * v⁻¹ := by rw [hyU]
        _ = _ := by group
    have h2 := (rootDiagUnit_conj_rootSL2 (thetaDiag δ (-1 : kˣ)) isRoot_thetaE6
      ((l : k) * 1)).1
    rw [mul_inv_eq_iff_eq_mul.2 h1] at h2
    have h3 := uSL_injective_E6 (hinj h2)
    have h4 : ((rootChar (thetaDiag δ (-1 : kˣ)) thetaE6 : kˣ) : k) = 1 := by
      have hl : (l : k) * 1 ≠ 0 := by simp
      exact mul_right_cancel₀ hl (h3.symm.trans (one_mul _).symm)
    exact Units.ext h4
  have hev : Even (iform thetaE6 δ) := by
    rw [iform_comm]
    refine even_of_neg_one_zpow_eq_one_E6 hk ?_
    rw [← rootChar_thetaDiag]
    exact hχ
  have hdθ := rootDiagUnit_thetaDiag_comm_levi' (τ := .E6) (k := k) thetaE6 (-1 : kˣ)
    (J := JE6) (fun j hj => iform_single_thetaE6_of_mem hj) hv
  rcases eq_or_iform_eq_zero_of_even_E6 hδ hev with rfl | rfl | h0
  · left
    calc y = v⁻¹ * (v * y * v⁻¹) * v := by group
      _ = v⁻¹ * (rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : kˣ)) * v) := by rw [hva]; group
      _ = v⁻¹ * (v * rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : kˣ))) := by rw [hdθ]
      _ = _ := by group
  · left
    rw [thetaDiag_neg_E6] at hva
    calc y = v⁻¹ * (v * y * v⁻¹) * v := by group
      _ = v⁻¹ * (rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : kˣ)) * v) := by rw [hva]; group
      _ = v⁻¹ * (v * rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : kˣ))) := by rw [hdθ]
      _ = _ := by group
  · right
    obtain ⟨n, hn, hnδ⟩ := exists_levi_conj_thetaDiag_alpha4 (k := k) hδ h0
    have hvy : (n * v) * y * (n * v)⁻¹ = rootDiagUnit .E6 (thetaDiag alpha4E6 (-1 : kˣ)) := by
      rw [← hnδ, ← hva]
      group
    exact exists_levi_fixed_conj_E6 p hp2 he isRoot_alpha4E6 iform_thetaE6_alpha4E6
      perm_alpha4E6 (mul_mem hn hv) hFy hvy

end Glue

end CFSG.ClassicalInvolution.ModelFacts.LeviE6
