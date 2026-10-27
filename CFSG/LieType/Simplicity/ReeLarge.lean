module

public import CFSG.LieType.Simplicity.ReeSmall
public import CFSG.LieType.Simplicity.ReeCells

public section

namespace CFSG.LieType.Simplicity

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree ReeTag

section Fixed

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

variable (t K a) in
noncomputable abbrev nrepFixed
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee) : reeFixed t K a :=
  ⟨nrep t.tag K w, nrep_mem_reeFixed t K a hw⟩

theorem exists_mul_nrepFixed_mul
    {v v' : WeylGroup t.tag} (hv : v ∈ t.relWeylRee)
    (hv' : v' ∈ t.relWeylRee)
    (hlen : (coxeterSystem t.tag).length (v * v') =
      (coxeterSystem t.tag).length v + (coxeterSystem t.tag).length v')
    {b : reeFixed t K a} (hb : b ∈ reeBorelPart t K a) :
    ∃ b₁ ∈ reeBorelPart t K a, ∃ b₂ ∈ reeBorelPart t K a,
      nrepFixed t K a hv * b * nrepFixed t K a hv' =
        b₁ * nrepFixed t K a (mul_mem hv hv') * b₂ := by
  obtain ⟨b₁, hb₁, hb₁F, b₂, hb₂, hb₂F, h⟩ :=
    exists_reeFixed_nrep_mul_mul_nrep_eq hv hv' hlen hb b.2
  exact ⟨⟨b₁, hb₁F⟩, hb₁, ⟨b₂, hb₂F⟩, hb₂, Subtype.ext h⟩

theorem length_wordProd_mul_of_isReduced
    {ω ω' : List (Fin t.tag.rank)}
    (hred : (coxeterSystem t.tag).IsReduced (ω ++ ω')) :
    (coxeterSystem t.tag).length
        ((coxeterSystem t.tag).wordProd ω * (coxeterSystem t.tag).wordProd ω') =
      (coxeterSystem t.tag).length ((coxeterSystem t.tag).wordProd ω) +
        (coxeterSystem t.tag).length ((coxeterSystem t.tag).wordProd ω') := by
  obtain ⟨h1, h2⟩ := isReduced_left_right_of_append hred
  rw [← CoxeterSystem.wordProd_append, hred.eq, h1.eq, h2.eq, List.length_append]

theorem nrepFixed_blockElt_mem
    {P : Subgroup (reeFixed t K a)} (hBP : reeBorelPart t K a ≤ P)
    (i : Fin t.tag.rank) {ω' : List (Fin t.tag.rank)}
    (hred : (coxeterSystem t.tag).IsReduced (t.reeOrbitWord i ++ ω'))
    (hω' : (coxeterSystem t.tag).wordProd ω' ∈ t.relWeylRee)
    (hP : nrepFixed t K a (mul_mem (reeOrbitWord_mem t i) hω') ∈ P) :
    nrepFixed t K a (reeOrbitWord_mem t i) ∈ P := by
  set r := nrepFixed t K a (reeOrbitWord_mem t i)
  set u := nrepFixed t K a hω'
  have hru : nrepFixed t K a (mul_mem (reeOrbitWord_mem t i) hω') = r * u := by
    apply Subtype.ext
    change nrep t.tag K ((coxeterSystem t.tag).wordProd (t.reeOrbitWord i) *
      (coxeterSystem t.tag).wordProd ω') = _
    rw [nrep_mul_of_isReduced_append K hred]
    rfl
  rw [hru] at hP
  have hconj : ∀ b ∈ reeBorelPart t K a, r * b * r⁻¹ ∈ P := by
    intro b hb
    obtain ⟨b₁, hb₁, b₂, hb₂, h⟩ := exists_mul_nrepFixed_mul (reeOrbitWord_mem t i) hω'
      (length_wordProd_mul_of_isReduced hred) hb
    rw [hru] at h
    have e : r * b * r⁻¹ = (r * b * u) * (r * u)⁻¹ := by group
    rw [e, h]
    exact mul_mem (mul_mem (mul_mem (hBP hb₁) hP) (hBP hb₂)) (inv_mem hP)
  obtain ⟨u₀, hu₀, hu₀F, b₁, hb₁, hb₁F, b₂, hb₂, hb₂F, h⟩ := exists_nrep_blockElt_eq t K a i
  have e : r = ⟨b₁, hb₁F⟩ * (r * ⟨u₀, hu₀F⟩ * r⁻¹) * ⟨b₂, hb₂F⟩ := Subtype.ext h
  rw [e]
  exact mul_mem (mul_mem (hBP hb₁) (hconj _ ((nativeData t.tag K).U_le_B hu₀))) (hBP hb₂)

theorem le_center_of_le_reeBorelPart
    (hgen : Subgroup.normalClosure (reeUnipPart t K a : Set (reeFixed t K a)) = ⊤)
    (M : Subgroup (reeFixed t K a)) [hM : M.Normal] (hMB : M ≤ reeBorelPart t K a) :
    M ≤ Subgroup.center (reeFixed t K a) := by
  refine le_center_of_inf_eq_bot hMB (fun b hb u hu => ?_) ?_ hgen
  · exact (Subgroup.mem_normalizer_iff.mp
      ((nativeRootSubgroups t.tag K).B_le_normalizer_U hb) _).mp hu
  · rw [eq_bot_iff]
    rintro u ⟨huM, huS⟩
    rw [Subgroup.mem_bot]
    have h := hMB (hM.conj_mem u huM (reeLongRep t K a))
    exact Subtype.ext (eq_one_of_nrep_longWord_conj_mem_B huS h)

end Fixed

@[expose] def relWords : (t : ReeTag) → List (List (Fin t.tag.rank))
  | .G2 => ([[], [0, 1, 0, 1, 0, 1]] : List (List (Fin 2)))
  | .F4 =>
    let A : List (Fin 4) := [0, 3]
    let B : List (Fin 4) := [1, 2, 1, 2]
    ([[], A, B, A ++ B, B ++ A, A ++ B ++ A, B ++ A ++ B, A ++ B ++ A ++ B, B ++ A ++ B ++ A,
      A ++ B ++ A ++ B ++ A, B ++ A ++ B ++ A ++ B, A ++ B ++ A ++ B ++ A ++ B,
      B ++ A ++ B ++ A ++ B ++ A, A ++ B ++ A ++ B ++ A ++ B ++ A,
      B ++ A ++ B ++ A ++ B ++ A ++ B, A ++ B ++ A ++ B ++ A ++ B ++ A ++ B,
      B ++ A ++ B ++ A ++ B ++ A ++ B ++ A] : List (List (Fin 4)))

theorem relWords_closed (t : ReeTag) : ∀ i : Fin t.tag.rank, ∀ ω ∈ relWords t,
    ∃ ω' ∈ relWords t, ∀ k : Fin t.tag.rank,
      (t.reeOrbitWord i ++ ω).foldr (reflect t.tag) (Pi.single k 1) =
        ω'.foldr (reflect t.tag) (Pi.single k 1) := by
  cases t <;> decide +kernel

theorem relWords_reducedCheck (t : ReeTag) : ∀ ω ∈ relWords t, reducedCheck t.tag ω = true := by
  cases t <;> decide +kernel

theorem relWords_fixed (t : ReeTag) : ∀ ω ∈ relWords t, ∀ k : Fin t.tag.rank,
    (ω.map t.perm).foldr (reflect t.tag) (Pi.single k 1) =
      ω.foldr (reflect t.tag) (Pi.single k 1) := by
  cases t <;> decide +kernel

theorem relWords_head (t : ReeTag) : ∀ ω ∈ relWords t, ω = [] ∨
    ∃ i : Fin t.tag.rank, ∃ ω' ∈ relWords t, ω = t.reeOrbitWord i ++ ω' := by
  cases t <;> decide

theorem nil_mem_relWords (t : ReeTag) : [] ∈ relWords t := by
  cases t <;> decide

theorem relWords_F4_triple :
    ReeTag.F4.reeOrbitWord (0 : Fin 4) ++
        (ReeTag.F4.reeOrbitWord (1 : Fin 4) ++ ReeTag.F4.reeOrbitWord (0 : Fin 4)) ∈
      relWords ReeTag.F4 ∧
    ReeTag.F4.reeOrbitWord (1 : Fin 4) ++
        (ReeTag.F4.reeOrbitWord (0 : Fin 4) ++ ReeTag.F4.reeOrbitWord (1 : Fin 4)) ∈
      relWords ReeTag.F4 := by
  decide

theorem wordProd_mem_relWeylRee_of_mem_relWords
    {t : ReeTag} {ω : List (Fin t.tag.rank)}
    (hω : ω ∈ relWords t) : (coxeterSystem t.tag).wordProd ω ∈ t.relWeylRee := by
  rw [mem_relWeylRee, weylPerm_wordProd]
  refine ext_single fun k => ?_
  rw [CFSG.LieType.Ree.wordProd_smul, CFSG.LieType.Ree.wordProd_smul]
  exact relWords_fixed t ω hω k

theorem isReduced_of_mem_relWords
    {t : ReeTag} {ω : List (Fin t.tag.rank)}
    (hω : ω ∈ relWords t) : (coxeterSystem t.tag).IsReduced ω :=
  isReduced_of_reducedCheck (relWords_reducedCheck t ω hω)

theorem exists_mem_relWords
    {t : ReeTag} {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee) :
    ∃ ω ∈ relWords t, w = (coxeterSystem t.tag).wordProd ω := by
  have hcl := t.mem_closure_blockElt _ w rfl ((mem_relWeylRee _).1 hw)
  clear hw
  have key : ∀ i : Fin t.tag.rank, ∀ ω ∈ relWords t, ∃ ω' ∈ relWords t,
      t.blockElt i * (coxeterSystem t.tag).wordProd ω = (coxeterSystem t.tag).wordProd ω' := by
    intro i ω hω
    obtain ⟨ω', hω', h⟩ := relWords_closed t i ω hω
    refine ⟨ω', hω', ext_single fun k => ?_⟩
    rw [blockElt, ← CoxeterSystem.wordProd_append, CFSG.LieType.Ree.wordProd_smul,
      CFSG.LieType.Ree.wordProd_smul]
    exact h k
  induction hcl using Subgroup.closure_induction_left with
  | one => exact ⟨[], nil_mem_relWords t, rfl⟩
  | mul_left x hx y _ ih =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨ω, hω, rfl⟩ := ih
    exact key i ω hω
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨ω, hω, rfl⟩ := ih
    have hinv : (t.blockElt i)⁻¹ = t.blockElt i :=
      inv_eq_of_mul_eq_one_right (t.blockElt_mul_self i)
    rw [hinv]
    exact key i ω hω

section Normal

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

theorem exists_nrepFixed_blockElt_mem
    {P : Subgroup (reeFixed t K a)}
    (hBP : reeBorelPart t K a ≤ P) {ω : List (Fin t.tag.rank)} (hω : ω ∈ relWords t)
    (hne : ω ≠ []) (hP : nrepFixed t K a (wordProd_mem_relWeylRee_of_mem_relWords hω) ∈ P) :
    ∃ i, nrepFixed t K a (reeOrbitWord_mem t i) ∈ P := by
  rcases relWords_head t ω hω with h | ⟨i, ω', hω', rfl⟩
  · exact absurd h hne
  refine ⟨i, nrepFixed_blockElt_mem hBP i (isReduced_of_mem_relWords hω)
    (wordProd_mem_relWeylRee_of_mem_relWords hω') ?_⟩
  convert hP using 1
  apply Subtype.ext
  change nrep t.tag K _ = nrep t.tag K _
  rw [CoxeterSystem.wordProd_append]

theorem nrepFixed_mul_self_mem_reeBorelPart
    (j : Fin t.tag.rank) :
    nrepFixed t K a (reeOrbitWord_mem t j) * nrepFixed t K a (reeOrbitWord_mem t j) ∈
      reeBorelPart t K a := by
  change nrep t.tag K (t.blockElt j) * nrep t.tag K (t.blockElt j) ∈ (nativeData t.tag K).B
  refine (nativeData t.tag K).H_le_B ((RootGroupData.mem_H_iff (D := nativeData t.tag K)).2
    ⟨⟨nrep t.tag K (t.blockElt j), nrep_mem_monomialGroup _ _ _⟩ *
      ⟨nrep t.tag K (t.blockElt j), nrep_mem_monomialGroup _ _ _⟩, ?_, rfl⟩)
  change weylHom t.tag K (⟨nrep t.tag K (t.blockElt j), nrep_mem_monomialGroup _ _ _⟩ *
    ⟨nrep t.tag K (t.blockElt j), nrep_mem_monomialGroup _ _ _⟩) = 1
  rw [map_mul, weylHom_nrep, t.blockElt_mul_self]

theorem eq_top_of_reeBorelPart_le
    {P : Subgroup (reeFixed t K a)} (hBP : reeBorelPart t K a ≤ P)
    (hn : ∀ i, nrepFixed t K a (reeOrbitWord_mem t i) ∈ P) : P = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hle : Subgroup.closure ({b | b ∈ (nativeData t.tag K).B ∧ b ∈ reeFixed t K a} ∪
      Set.range fun i => nrep t.tag K (t.blockElt i)) ≤ P.map (reeFixed t K a).subtype := by
    rw [Subgroup.closure_le]
    rintro x (⟨hxB, hxF⟩ | ⟨i, rfl⟩)
    · exact ⟨⟨x, hxF⟩, hBP hxB, rfl⟩
    · exact ⟨_, hn i, rfl⟩
  obtain ⟨y, hy, hyg⟩ := hle (mem_closure_of_mem_reeFixed g.2)
  rwa [Subtype.ext hyg] at hy

end Normal

section F4

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem nrepFixed_mem_sup_of_mem_F4
    (M : Subgroup (reeFixed ReeTag.F4 K a)) [hM : M.Normal]
    {i j : Fin 4} (hij : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0))
    (hi : nrepFixed ReeTag.F4 K a (reeOrbitWord_mem ReeTag.F4 i) ∈ M ⊔ reeBorelPart ReeTag.F4 K a) :
    nrepFixed ReeTag.F4 K a (reeOrbitWord_mem ReeTag.F4 j) ∈ M ⊔ reeBorelPart ReeTag.F4 K a := by
  set P := M ⊔ reeBorelPart ReeTag.F4 K a
  have hBP : reeBorelPart ReeTag.F4 K a ≤ P := le_sup_right
  set ni := nrepFixed ReeTag.F4 K a (reeOrbitWord_mem ReeTag.F4 i)
  set nj := nrepFixed ReeTag.F4 K a (reeOrbitWord_mem ReeTag.F4 j)
  have hji : ReeTag.F4.reeOrbitWord j ++ ReeTag.F4.reeOrbitWord i ∈ relWords ReeTag.F4 := by
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hjij : ReeTag.F4.reeOrbitWord j ++ (ReeTag.F4.reeOrbitWord i ++ ReeTag.F4.reeOrbitWord j) ∈
      relWords ReeTag.F4 := by
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact relWords_F4_triple.2
    · exact relWords_F4_triple.1
  have hij' : ReeTag.F4.reeOrbitWord i ++ ReeTag.F4.reeOrbitWord j ∈ relWords ReeTag.F4 := by
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hred_ji := isReduced_of_mem_relWords hji
  have hred_jij := isReduced_of_mem_relWords hjij
  have hmem_ji : ReeTag.F4.blockElt j * ReeTag.F4.blockElt i ∈ ReeTag.F4.relWeylRee :=
    mul_mem (reeOrbitWord_mem ReeTag.F4 j) (reeOrbitWord_mem ReeTag.F4 i)
  obtain ⟨m, hm, b, hb, hmb⟩ := Subgroup.mem_sup_of_normal_left.1 hi
  have hm' : nj * m * nj⁻¹ ∈ P := Subgroup.mem_sup_left (hM.conj_mem m hm nj)
  have hnji : nj * ni = nrepFixed ReeTag.F4 K a hmem_ji := by
    apply Subtype.ext
    exact (nrep_mul_of_isReduced_append K hred_ji).symm
  have hlen : (coxeterSystem ReeTag.F4.tag).length
      (ReeTag.F4.blockElt j * ReeTag.F4.blockElt i * ReeTag.F4.blockElt j) =
        (coxeterSystem ReeTag.F4.tag).length (ReeTag.F4.blockElt j * ReeTag.F4.blockElt i) +
          (coxeterSystem ReeTag.F4.tag).length (ReeTag.F4.blockElt j) := by
    have h1 : (ReeTag.F4.reeOrbitWord j ++ ReeTag.F4.reeOrbitWord i) ++
        ReeTag.F4.reeOrbitWord j =
          ReeTag.F4.reeOrbitWord j ++ (ReeTag.F4.reeOrbitWord i ++ ReeTag.F4.reeOrbitWord j) :=
      List.append_assoc _ _ _
    have h2 := length_wordProd_mul_of_isReduced (t := ReeTag.F4) (h1 ▸ hred_jij)
    rwa [CoxeterSystem.wordProd_append] at h2
  obtain ⟨d₁, hd₁, d₂, hd₂, hd⟩ :=
    exists_mul_nrepFixed_mul hmem_ji (reeOrbitWord_mem ReeTag.F4 j) hlen (inv_mem hb)
  have hv : nrepFixed ReeTag.F4 K a (mul_mem hmem_ji (reeOrbitWord_mem ReeTag.F4 j)) ∈ P := by
    have hc := nrepFixed_mul_self_mem_reeBorelPart (K := K) (a := a) (t := ReeTag.F4) j
    have e : nrepFixed ReeTag.F4 K a (mul_mem hmem_ji (reeOrbitWord_mem ReeTag.F4 j)) =
        d₁⁻¹ * (nj * m * nj⁻¹) * (d₂ * (nj * nj)⁻¹)⁻¹ := by
      have hm_eq : m = ni * b⁻¹ := by rw [← hmb]; group
      have e2 : nj * m * nj⁻¹ = (nj * ni) * b⁻¹ * nj * (nj * nj)⁻¹ := by
        rw [hm_eq]; group
      rw [e2, hnji, hd]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hBP hd₁)) hm') (inv_mem (mul_mem (hBP hd₂)
      (inv_mem (hBP hc))))
  refine nrepFixed_blockElt_mem hBP j hred_jij (wordProd_mem_relWeylRee_of_mem_relWords hij') ?_
  convert hv using 1
  apply Subtype.ext
  change nrep ReeTag.F4.tag K _ = nrep ReeTag.F4.tag K _
  rw [CoxeterSystem.wordProd_append, mul_assoc]

theorem sup_reeBorelPart_eq_top_F4
    (M : Subgroup (reeFixed ReeTag.F4 K a)) [hM : M.Normal]
    (hMB : ¬ M ≤ reeBorelPart ReeTag.F4 K a) : M ⊔ reeBorelPart ReeTag.F4 K a = ⊤ := by
  set P := M ⊔ reeBorelPart ReeTag.F4 K a
  have hBP : reeBorelPart ReeTag.F4 K a ≤ P := le_sup_right
  obtain ⟨g, hgM, hgB⟩ := Set.not_subset.1 hMB
  obtain ⟨w, hw, b₁, hb₁, hb₁F, b₂, hb₂, hb₂F, hg⟩ := reeFixed_bruhat ReeTag.F4 K a g g.2
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hgB
    change (g : adjointGroup ReeTag.F4.tag K) ∈ (nativeData ReeTag.F4.tag K).B
    rw [hg, nrep_one, mul_one]
    exact mul_mem hb₁ hb₂
  have hnw : nrepFixed ReeTag.F4 K a hw ∈ P := by
    have e : nrepFixed ReeTag.F4 K a hw = (⟨b₁, hb₁F⟩ : reeFixed ReeTag.F4 K a)⁻¹ * g *
        (⟨b₂, hb₂F⟩ : reeFixed ReeTag.F4 K a)⁻¹ := by
      apply Subtype.ext
      change nrep ReeTag.F4.tag K w = b₁⁻¹ * (g : adjointGroup ReeTag.F4.tag K) * b₂⁻¹
      rw [hg]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hBP hb₁)) (Subgroup.mem_sup_left hgM)) (inv_mem (hBP hb₂))
  obtain ⟨ω, hω, rfl⟩ := exists_mem_relWords hw
  have hne : ω ≠ [] := by
    rintro rfl
    exact hw1 rfl
  obtain ⟨i, hi⟩ := exists_nrepFixed_blockElt_mem hBP hω hne hnw
  have h01 : nrepFixed ReeTag.F4 K a (reeOrbitWord_mem ReeTag.F4 (0 : Fin 4)) ∈ P ∧
      nrepFixed ReeTag.F4 K a (reeOrbitWord_mem ReeTag.F4 (1 : Fin 4)) ∈ P := by
    have h0 : ∀ k : Fin 4, k = 0 ∨ k = 3 → nrepFixed ReeTag.F4 K a (reeOrbitWord_mem ReeTag.F4 k) =
        nrepFixed ReeTag.F4 K a (reeOrbitWord_mem ReeTag.F4 (0 : Fin 4)) := by
      rintro k (rfl | rfl) <;> rfl
    have h1 : ∀ k : Fin 4, k = 1 ∨ k = 2 → nrepFixed ReeTag.F4 K a (reeOrbitWord_mem ReeTag.F4 k) =
        nrepFixed ReeTag.F4 K a (reeOrbitWord_mem ReeTag.F4 (1 : Fin 4)) := by
      rintro k (rfl | rfl) <;> rfl
    have hcases : ∀ k : Fin 4, (k = 0 ∨ k = 3) ∨ (k = 1 ∨ k = 2) := by decide
    rcases hcases i with hk | hk
    · rw [h0 i hk] at hi
      exact ⟨hi, nrepFixed_mem_sup_of_mem_F4 M (.inl ⟨rfl, rfl⟩) hi⟩
    · rw [h1 i hk] at hi
      exact ⟨nrepFixed_mem_sup_of_mem_F4 M (.inr ⟨rfl, rfl⟩) hi, hi⟩
  refine eq_top_of_reeBorelPart_le hBP fun k => ?_
  have hcases : ∀ k : Fin 4, (k = 0 ∨ k = 3) ∨ (k = 1 ∨ k = 2) := by decide
  rcases hcases k with (rfl | rfl) | (rfl | rfl)
  · exact h01.1
  · exact h01.1
  · exact h01.2
  · exact h01.2

end F4

end CFSG.LieType.Simplicity
