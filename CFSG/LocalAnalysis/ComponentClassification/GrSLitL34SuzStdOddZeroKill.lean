module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroDefs
public import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
public import CFSG.SignalizerFunctorTheorem.Inheritance.Quotient
public import CFSG.GH74.E2.TermBasic
public import CFSG.GroupTheory.Commutator.SubgroupOf
public import CFSG.GH74.Constrained
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem map_mulAut_mul {Y : Type} [Group Y] (H : Subgroup Y) (A B : MulAut Y) :
    H.map (A * B).toMonoidHom = (H.map B.toMonoidHom).map A.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem isComponent_map_conj {Y : Type} [Group Y] {L : Subgroup Y}
    (hL : IsComponent L) (y : Y) :
    IsComponent (L.map (MulAut.conj y).toMonoidHom) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj y) hL

private theorem map_conj_eq_of_commute {Y : Type} [Group Y] [Finite Y] {D : Subgroup Y} {y : Y}
    (hy : ∀ d ∈ D, d * y = y * d) :
    D.map (MulAut.conj y).toMonoidHom = D := by
  have key : ∀ d ∈ D, (MulAut.conj y) d ∈ D := by
    intro d hd
    have h : y * d * y⁻¹ = d := by
      rw [← hy d hd]
      group
    simpa only [MulAut.conj_apply, h] using hd
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro d ⟨e, he, rfl⟩
    exact key e he
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj y).toMonoidHom) (MulAut.conj y).injective]

private theorem conj_pair_images {Y : Type} [Group Y] [Finite Y] {D L M : Subgroup Y} {y : Y}
    (hL : IsComponent L) (hM : IsComponent M)
    (hchar : ∀ L' : Subgroup Y, IsComponent L' → (⁅D, L'⁆ ≠ ⊥ ↔ L' = L ∨ L' = M))
    (hyD : ∀ d ∈ D, d * y = y * d) :
    (L.map (MulAut.conj y).toMonoidHom = L ∨ L.map (MulAut.conj y).toMonoidHom = M) ∧
    (M.map (MulAut.conj y).toMonoidHom = L ∨ M.map (MulAut.conj y).toMonoidHom = M) := by
  have hyDmap : D.map (MulAut.conj y).toMonoidHom = D := map_conj_eq_of_commute hyD
  have key : ∀ L' : Subgroup Y, ⁅D, L'⁆ ≠ ⊥ →
      ⁅D, L'.map (MulAut.conj y).toMonoidHom⁆ ≠ ⊥ := by
    intro L' hL'
    have hmap : ⁅D, L'.map (MulAut.conj y).toMonoidHom⁆ =
        (⁅D, L'⁆).map (MulAut.conj y).toMonoidHom := by
      rw [Subgroup.map_commutator, hyDmap]
    rw [hmap]
    intro hbot
    exact hL' ((Subgroup.map_eq_bot_iff_of_injective (⁅D,L'⁆) (MulAut.conj y).injective).mp hbot)
  exact ⟨(hchar _ (isComponent_map_conj hL y)).mp (key L ((hchar L hL).mpr (Or.inl rfl))),
    (hchar _ (isComponent_map_conj hM y)).mp (key M ((hchar M hM).mpr (Or.inr rfl)))⟩

private theorem map_eq_of_fixes {Y : Type} [Group Y] {A : MulAut Y} {L M : Subgroup Y}
    (hLM : L ≠ M) (hA : L.map A.toMonoidHom = L)
    (hM : M.map A.toMonoidHom = L ∨ M.map A.toMonoidHom = M) :
    M.map A.toMonoidHom = M :=
  hM.resolve_left fun h =>
    hLM (Subgroup.map_injective (f := A.toMonoidHom) A.injective (hA.trans h.symm))

private theorem map_eq_of_swaps {Y : Type} [Group Y] {A : MulAut Y} {L M : Subgroup Y}
    (hLM : L ≠ M) (hA : L.map A.toMonoidHom = M)
    (hM : M.map A.toMonoidHom = L ∨ M.map A.toMonoidHom = M) :
    M.map A.toMonoidHom = L :=
  hM.resolve_right fun h =>
    hLM (Subgroup.map_injective (f := A.toMonoidHom) A.injective (hA.trans h.symm))

private theorem map_inv_eq_of_fixes {Y : Type} [Group Y] {A : MulAut Y} {L M : Subgroup Y}
    (hL : L.map A.toMonoidHom = L) (hM : M.map A.toMonoidHom = M) :
    L.map (A⁻¹).toMonoidHom = L ∧ M.map (A⁻¹).toMonoidHom = M := by
  constructor
  · refine Subgroup.map_injective (f := A.toMonoidHom) A.injective ?_
    rw [← map_mulAut_mul]
    rw [show A * A⁻¹ = 1 by simp]
    rw [hL]
    change L.map (MonoidHom.id Y) = L
    rw [Subgroup.map_id]
  · refine Subgroup.map_injective (f := A.toMonoidHom) A.injective ?_
    rw [← map_mulAut_mul]
    rw [show A * A⁻¹ = 1 by simp]
    rw [hM]
    change M.map (MonoidHom.id Y) = M
    rw [Subgroup.map_id]

private theorem map_inv_eq_of_swaps {Y : Type} [Group Y] {A : MulAut Y} {L M : Subgroup Y}
    (hL : L.map A.toMonoidHom = M) (hM : M.map A.toMonoidHom = L) :
    L.map (A⁻¹).toMonoidHom = M ∧ M.map (A⁻¹).toMonoidHom = L := by
  constructor
  · refine Subgroup.map_injective (f := A.toMonoidHom) A.injective ?_
    rw [← map_mulAut_mul]
    rw [show A * A⁻¹ = 1 by simp]
    rw [hM]
    change L.map (MonoidHom.id Y) = L
    rw [Subgroup.map_id]
  · refine Subgroup.map_injective (f := A.toMonoidHom) A.injective ?_
    rw [← map_mulAut_mul]
    rw [show A * A⁻¹ = 1 by simp]
    rw [hL]
    change M.map (MonoidHom.id Y) = M
    rw [Subgroup.map_id]

private theorem map_conj_commutatorElement_eq {Y : Type} [Group Y] {L M : Subgroup Y} {u v : Y}
    (hLM : L ≠ M)
    (hu : L.map (MulAut.conj u).toMonoidHom = L ∨ L.map (MulAut.conj u).toMonoidHom = M)
    (hu' : M.map (MulAut.conj u).toMonoidHom = L ∨ M.map (MulAut.conj u).toMonoidHom = M)
    (hv : L.map (MulAut.conj v).toMonoidHom = L ∨ L.map (MulAut.conj v).toMonoidHom = M)
    (hv' : M.map (MulAut.conj v).toMonoidHom = L ∨ M.map (MulAut.conj v).toMonoidHom = M) :
    L.map (MulAut.conj ⁅u, v⁆).toMonoidHom = L := by
  have hcomm : (MulAut.conj ⁅u, v⁆).toMonoidHom =
      ((MulAut.conj u * MulAut.conj v * (MulAut.conj u)⁻¹ * (MulAut.conj v)⁻¹) :
        MulAut Y).toMonoidHom := by
    congr 1
    rw [commutatorElement_def, map_mul MulAut.conj, map_mul MulAut.conj,
      map_mul MulAut.conj, map_inv, map_inv]
  rw [hcomm, map_mulAut_mul, map_mulAut_mul, map_mulAut_mul]
  rcases hu with hA | hA <;> rcases hv with hB | hB
  · have hMA := map_eq_of_fixes hLM hA hu'
    have hAi := map_inv_eq_of_fixes hA hMA
    have hMB := map_eq_of_fixes hLM hB hv'
    have hBi := map_inv_eq_of_fixes hB hMB
    rw [hBi.1, hAi.1, hB, hA]
  · have hMA := map_eq_of_fixes hLM hA hu'
    have hAi := map_inv_eq_of_fixes hA hMA
    have hMB := map_eq_of_swaps hLM hB hv'
    have hBi := map_inv_eq_of_swaps hB hMB
    rw [hBi.1, hAi.2, hMB, hA]
  · have hMA := map_eq_of_swaps hLM hA hu'
    have hAi := map_inv_eq_of_swaps hA hMA
    have hMB := map_eq_of_fixes hLM hB hv'
    have hBi := map_inv_eq_of_fixes hB hMB
    rw [hBi.1, hAi.1, hMB, hMA]
  · have hMA := map_eq_of_swaps hLM hA hu'
    have hAi := map_inv_eq_of_swaps hA hMA
    have hMB := map_eq_of_swaps hLM hB hv'
    have hBi := map_inv_eq_of_swaps hB hMB
    rw [hBi.1, hAi.2, hB, hMA]

private theorem commutator_le_normalizer_of_pair {Y : Type} [Group Y] [Finite Y]
    {D L M : Subgroup Y} (hLM : L ≠ M) (hL : IsComponent L) (hM : IsComponent M)
    (hchar : ∀ L' : Subgroup Y, IsComponent L' → (⁅D, L'⁆ ≠ ⊥ ↔ L' = L ∨ L' = M))
    (H : Subgroup Y) (hH : ∀ h ∈ H, ∀ d ∈ D, d * h = h * d) :
    ⁅H, H⁆ ≤ Subgroup.normalizer (L : Set Y) := by
  rw [Subgroup.commutator_le]
  intro u hu v hv
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hu' := conj_pair_images hL hM hchar (hH u hu)
  have hv' := conj_pair_images hL hM hchar (hH v hv)
  exact map_conj_commutatorElement_eq hLM hu'.1 hu'.2 hv'.1 hv'.2

omit [Finite G] in
private theorem image_centralizes {b : G} {P : Subgroup G}
    {y : ↥(centralizer ({b} : Set G))}
    (hyP : (y : G) ∈ centralizer (P : Set G)) :
    ∀ d ∈ (P.subgroupOf (centralizer ({b} : Set G))).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({b} : Set G)))),
      d * QuotientGroup.mk' _ y = QuotientGroup.mk' _ y * d := by
  rintro d ⟨p, hp, rfl⟩
  have hpP : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
  have hcomm : p * y = y * p := by
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hyP (p : G) hpP
  rw [← map_mul, ← map_mul, hcomm]

theorem false_of_l34ZeroSwappedBar_of_mem_commutator {x b : G}
    {hxb : x ∈ centralizer ({b} : Set G)} {P : Subgroup G} (h : L34ZeroSwappedBar x b hxb P)
    {Y : Subgroup G} (hYP : Y ≤ centralizer (P : Set G)) (hYb : Y ≤ centralizer ({b} : Set G))
    (hxY : x ∈ ⁅Y, Y⁆) : False := by
  classical
  obtain ⟨L, hLcomp, hLne, hLchar⟩ := h
  let Cb : Subgroup G := centralizer ({b} : Set G)
  let O : Subgroup ↥Cb := pPrimeCore 2 ↥Cb
  let π : ↥Cb →* (↥Cb ⧸ O) := QuotientGroup.mk' O
  let Yx : Subgroup ↥Cb := Y.subgroupOf Cb
  let Lx : Subgroup (↥Cb ⧸ O) := L.map (MulAut.conj (π ⟨x, hxb⟩)).toMonoidHom
  have hLxcomp : IsComponent Lx := isComponent_map_conj hLcomp _
  have hLM : L ≠ Lx := fun h' => hLne h'.symm
  have hcent : ∀ h' ∈ Yx.map π, ∀ d ∈ (P.subgroupOf Cb).map π, d * h' = h' * d := by
    rintro _ ⟨u, hu, rfl⟩ d hd
    exact image_centralizes (P := P) (y := u) (hYP (Subgroup.mem_subgroupOf.mp hu)) d hd
  have hcomm_le : ⁅Yx.map π, Yx.map π⁆ ≤ Subgroup.normalizer (L : Set (↥Cb ⧸ O)) :=
    commutator_le_normalizer_of_pair hLM hLcomp hLxcomp hLchar _ hcent
  have hxYmem : x ∈ Y := Subgroup.commutator_le_self Y hxY
  have hxX : x ∈ Cb := hYb hxYmem
  have hxYx : (⟨x, hxX⟩ : ↥Cb) ∈ ⁅Yx, Yx⁆ := by
    change (⟨x, hxX⟩ : ↥Cb) ∈ ⁅Y.subgroupOf Cb, Y.subgroupOf Cb⁆
    rw [CFSG.GroupTheory.commutator_subgroupOf_eq hYb hYb]
    exact hxY
  have hxH : π ⟨x, hxX⟩ ∈ ⁅Yx.map π, Yx.map π⁆ := by
    have h := Subgroup.mem_map_of_mem π hxYx
    rwa [Subgroup.map_commutator] at h
  have hfix : L.map (MulAut.conj (π ⟨x, hxX⟩)).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hcomm_le hxH)
  have hxx : (⟨x, hxX⟩ : ↥Cb) = ⟨x, hxb⟩ := Subtype.ext rfl
  rw [hxx] at hfix
  exact hLne hfix

private theorem isComponent_map_centralizer {X : Type} [Group X] [Finite X]
    {v : X} (hv : v ^ 2 = 1) {P : Subgroup X}
    (hPv : P ≤ centralizer ({v} : Set X))
    (hP : IsComponent (P.subgroupOf (centralizer ({v} : Set X))))
    (hDne : P.map (QuotientGroup.mk' (pPrimeCore 2 X)) ≠ ⊥) :
    P.map (QuotientGroup.mk' (pPrimeCore 2 X)) ≤
        centralizer ({QuotientGroup.mk' (pPrimeCore 2 X) v} : Set (X ⧸ pPrimeCore 2 X)) ∧
      IsComponent ((P.map (QuotientGroup.mk' (pPrimeCore 2 X))).subgroupOf
        (centralizer ({QuotientGroup.mk' (pPrimeCore 2 X) v} : Set (X ⧸ pPrimeCore 2 X)))) := by
  classical
  let O : Subgroup X := pPrimeCore 2 X
  let π : X →* (X ⧸ O) := QuotientGroup.mk' O
  let C : Subgroup X := centralizer ({v} : Set X)
  let Cq : Subgroup (X ⧸ O) := centralizer ({π v} : Set (X ⧸ O))
  have hOodd : Odd (Nat.card O) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := X))
  have hzv : IsPGroup 2 (Subgroup.zpowers v) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hv) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hCmap : C.map π = Cq := by
    have h := CFSG.SignalizerFunctorTheorem.map_inf_centralizer_eq (H := X) (p := 2) Nat.prime_two
      (W := ⊤) (N := O) le_top (Nat.coprime_two_left.mpr hOodd) hv
    rw [top_inf_eq, Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective O),
      top_inf_eq] at h
    simpa [C, Cq, π] using h
  let φ : ↥C →* ↥Cq :=
    ((MulEquiv.subgroupCongr hCmap).toMonoidHom).comp (π.subgroupMap C)
  have hφval : ∀ x : ↥C, ((φ x : ↥Cq) : X ⧸ O) = π (x : X) := by
    intro x
    change ((MulEquiv.subgroupCongr hCmap (π.subgroupMap C x) : ↥Cq) : X ⧸ O) = π (x : X)
    rw [MulEquiv.subgroupCongr_apply]
    rfl
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := MonoidHom.subgroupMap_surjective π C ((MulEquiv.subgroupCongr hCmap).symm y)
    have hx' : MulEquiv.subgroupCongr hCmap (π.subgroupMap C x) = y := by
      rw [hx]
      exact (MulEquiv.subgroupCongr hCmap).apply_symm_apply y
    refine ⟨x, ?_⟩
    apply Subtype.ext
    rw [hφval]
    exact congrArg Subtype.val hx'
  have hnotle : ¬ (P.subgroupOf C) ≤ φ.ker := by
    intro hle
    apply hDne
    rw [Subgroup.map_eq_bot_iff]
    intro p hp
    have hpC : p ∈ C := hPv hp
    have h1 : φ ⟨p, hpC⟩ = 1 := hle (Subgroup.mem_subgroupOf.mpr hp)
    have h2 : π p = 1 := by
      have := congrArg (fun z : ↥Cq => (z : X ⧸ O)) h1
      simpa [hφval] using this
    exact (QuotientGroup.eq_one_iff (x := p)).mp (by simpa [π, QuotientGroup.mk'_apply] using h2)
  have hmap : (P.subgroupOf C).map φ = (P.map π).subgroupOf Cq := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mp hx))
    · intro hy
      obtain ⟨p, hp, hpy⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hy)
      refine ⟨⟨p, hPv hp⟩, Subgroup.mem_subgroupOf.mpr hp, ?_⟩
      apply Subtype.ext
      rw [hφval]
      exact hpy
  have hq : IsQuasisimple ↥((P.map π).subgroupOf Cq) := by
    rw [← hmap]
    exact CFSG.LocalCores.isQuasisimple_map hP.1 φ hnotle
  have hsub : ((P.map π).subgroupOf Cq).IsSubnormal := by
    rw [← hmap]
    exact hP.2.map hφsurj
  refine ⟨?_, hq, hsub⟩
  change P.map π ≤ Cq
  rw [← hCmap]
  exact Subgroup.map_mono hPv

private theorem false_of_component_orbit_fixed {Y : Type} [Group Y] [Finite Y]
    (hO : pPrimeCore 2 Y = ⊥) {t : Y} (ht : t ^ 2 = 1)
    {D L M : Subgroup Y} (hL : IsComponent L) (hM : IsComponent M) (hLne : M ≠ L)
    (hDt : D ≤ centralizer ({t} : Set Y))
    (hD : IsComponent (D.subgroupOf (centralizer ({t} : Set Y))))
    (hDtc : ∀ d ∈ D, d * t = t * d)
    (hchar : ∀ L' : Subgroup Y, IsComponent L' → (⁅D, L'⁆ ≠ ⊥ ↔ L' = L ∨ L' = M))
    (hfix : L.map (MulAut.conj t).toMonoidHom = L) : False := by
  obtain ⟨-, K, hKcomp, -, -, -, hKpair, -, -⟩ :=
    CFSG.SeitzReduction.exists_isComponent_orbit_of_isComponent_centralizer hO ht hDt hD
  have hDL : ⁅D, L⁆ ≠ ⊥ := (hchar L hL).mpr (Or.inl rfl)
  have hDM : ⁅D, M⁆ ≠ ⊥ := (hchar M hM).mpr (Or.inr rfl)
  have hMfix : M.map (MulAut.conj t).toMonoidHom = M := by
    rcases (conj_pair_images hL hM hchar hDtc).2 with h | h
    · exfalso
      exact hLne (Subgroup.map_injective (f := (MulAut.conj t).toMonoidHom)
        (MulAut.conj t).injective (h.trans hfix.symm))
    · exact h
  have hKfix : K.map (MulAut.conj t).toMonoidHom = K := by
    rcases (hchar K hKcomp).mp ((hKpair K hKcomp).mpr (Or.inl rfl)) with h | h
    · rw [h, hfix]
    · rw [h, hMfix]
  have hL_K : L = K := by
    rcases (hKpair L hL).mp hDL with h | h
    · exact h
    · rw [h, hKfix]
  have hM_K : M = K := by
    rcases (hKpair M hM).mp hDM with h | h
    · exact h
    · rw [h, hKfix]
  exact hLne (hM_K.trans hL_K.symm)

private theorem false_of_isComponent_fixed {x b v : G} {hxb : x ∈ centralizer ({b} : Set G)}
    {P : Subgroup G} (hPb : P ≤ centralizer ({b} : Set G))
    (hvX : v ∈ centralizer ({b} : Set G)) (hv2 : v * v = 1)
    (hPv : P ≤ centralizer ({v} : Set G))
    (hPcompv : IsComponent (P.subgroupOf (centralizer ({v} : Set G))))
    {L : Subgroup (↥(centralizer ({b} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({b} : Set G)))}
    (hLcomp : IsComponent L)
    (hLne : L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({b} : Set G)))
      ⟨x, hxb⟩)).toMonoidHom ≠ L)
    (hLchar : ∀ L' : Subgroup
        (↥(centralizer ({b} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({b} : Set G))),
      IsComponent L' → (⁅(P.subgroupOf (centralizer ({b} : Set G))).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({b} : Set G)))), L'⁆ ≠ ⊥ ↔
        L' = L ∨ L' = L.map (MulAut.conj (QuotientGroup.mk'
          (pPrimeCore 2 ↥(centralizer ({b} : Set G))) ⟨x, hxb⟩)).toMonoidHom))
    (hvfix : L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({b} : Set G)))
      ⟨v, hvX⟩)).toMonoidHom = L) :
    False := by
  classical
  let Cb : Subgroup G := centralizer ({b} : Set G)
  let O : Subgroup ↥Cb := pPrimeCore 2 ↥Cb
  let π : ↥Cb →* (↥Cb ⧸ O) := QuotientGroup.mk' O
  let D : Subgroup (↥Cb ⧸ O) := (P.subgroupOf Cb).map π
  let Lx : Subgroup (↥Cb ⧸ O) := L.map (MulAut.conj (π ⟨x, hxb⟩)).toMonoidHom
  let vX : ↥Cb := ⟨v, hvX⟩
  let vbar : ↥Cb ⧸ O := π vX
  have hLxcomp : IsComponent Lx := isComponent_map_conj (Y := ↥Cb ⧸ O) hLcomp _
  have hvfix' : L.map (MulAut.conj vbar).toMonoidHom = L := hvfix
  let Cg : Subgroup G := Cb ⊓ centralizer ({v} : Set G)
  have hPcompCg : IsComponent (P.subgroupOf Cg) :=
    CFSG.SeitzReduction.CentralizerComponents.isComponent_subgroupOf_inf_centralizer hPv hPcompv hPb
  let Cx : Subgroup ↥Cb := centralizer ({vX} : Set ↥Cb)
  have hCx : Cg.subgroupOf Cb = Cx := by
    ext y
    change (y : G) ∈ Cb ∧ (y : G) ∈ centralizer ({v} : Set G) ↔ y ∈ centralizer ({vX} : Set ↥Cb)
    constructor
    · rintro ⟨-, hy⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hy))
    · intro hy
      exact ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (by simpa using congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy))⟩
  have hPcompCx : IsComponent ((P.subgroupOf Cb).subgroupOf Cx) := by
    have h :=
      (CFSG.GH74.E2.isComponent_subgroupOf_iff (K := P) (M := Cg) (H := Cb) inf_le_left).2 hPcompCg
    rwa [hCx] at h
  have hvX2 : vX ^ 2 = 1 := by
    rw [pow_two]
    apply Subtype.ext
    simpa using hv2
  have hPleCx : (P.subgroupOf Cb) ≤ Cx := by
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hPv (Subgroup.mem_subgroupOf.mp hp)) v rfl).symm
  have hDne : D ≠ ⊥ := by
    intro hbot
    have hDL : ⁅D, L⁆ ≠ ⊥ := (hLchar L hLcomp).mpr (Or.inl rfl)
    rw [hbot] at hDL
    exact hDL (by simp)
  have hmap := isComponent_map_centralizer (X := ↥Cb) (v := vX) (P := P.subgroupOf Cb)
    hvX2 hPleCx hPcompCx (by simpa only [D] using hDne)
  have hOquot : pPrimeCore 2 (↥Cb ⧸ O) = ⊥ :=
    CFSG.GH74.pPrimeCore_quotient_pPrimeCore_eq_bot ↥Cb 2
  have hDt : D ≤ centralizer ({vbar} : Set (↥Cb ⧸ O)) := by
    simpa only [D, vbar] using hmap.1
  have hDcomp : IsComponent (D.subgroupOf (centralizer ({vbar} : Set (↥Cb ⧸ O)))) := by
    simpa only [D, vbar] using hmap.2
  have hvbar2 : vbar ^ 2 = 1 := by
    rw [pow_two]
    change π vX * π vX = 1
    rw [← map_mul, ← pow_two, hvX2, map_one]
  have hDv : ∀ d ∈ D, d * vbar = vbar * d := by
    rintro d ⟨p, hp, rfl⟩
    have hpP : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
    have hcomm : p * vX = vX * p := by
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (hPv hpP) v rfl).symm
    change π p * π vX = π vX * π p
    rw [← map_mul, ← map_mul, hcomm]
  exact false_of_component_orbit_fixed hOquot hvbar2 hLcomp hLxcomp (by simpa only [Lx] using hLne)
    hDt hDcomp hDv (by simpa only [Lx] using hLchar) hvfix'

theorem false_of_l34ZeroSwappedBar_of_four {x b : G} {hxb : x ∈ centralizer ({b} : Set G)}
    {P : Subgroup G} (h : L34ZeroSwappedBar x b hxb P) (hPb : P ≤ centralizer ({b} : Set G))
    {U : Subgroup G} (hUP : U ≤ centralizer (P : Set G)) (hUb : U ≤ centralizer ({b} : Set G))
    (hU4 : Nat.card U = 4) (hU2 : ∀ v ∈ U, v * v = 1)
    (hUc : ∀ v ∈ U, v ≠ 1 → P ≤ centralizer ({v} : Set G) ∧
      IsComponent (P.subgroupOf (centralizer ({v} : Set G)))) : False := by
  classical
  obtain ⟨L, hLcomp, hLne, hLchar⟩ := h
  let Cb : Subgroup G := centralizer ({b} : Set G)
  let O : Subgroup ↥Cb := pPrimeCore 2 ↥Cb
  let π : ↥Cb →* (↥Cb ⧸ O) := QuotientGroup.mk' O
  let Lx : Subgroup (↥Cb ⧸ O) := L.map (MulAut.conj (π ⟨x, hxb⟩)).toMonoidHom
  have hLxcomp : IsComponent Lx := isComponent_map_conj (Y := ↥Cb ⧸ O) hLcomp _
  have hLM : L ≠ Lx := fun h' => hLne h'.symm
  have hUne : U ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hU4
    omega
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
  let aG : G := (a : G)
  have haU : aG ∈ U := a.2
  have ha1 : aG ≠ 1 := fun h' => ha (Subtype.ext h')
  have hcard_a : Nat.card (Subgroup.zpowers aG) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by simpa [pow_two] using hU2 aG haU) ha1
  have hneq_a : Subgroup.zpowers aG ≠ U := by
    intro hEq
    rw [← hEq, hcard_a] at hU4
    omega
  have hnotle : ¬ U ≤ Subgroup.zpowers aG := by
    intro hle
    exact hneq_a (le_antisymm (Subgroup.zpowers_le.mpr haU) hle)
  obtain ⟨c, hcU, hcnot⟩ := Set.not_subset.mp hnotle
  have hc1 : c ≠ 1 := fun h' => hcnot (h'.symm ▸ Subgroup.one_mem (Subgroup.zpowers aG))
  have hca : c ≠ aG := fun h' => hcnot (h' ▸ Subgroup.mem_zpowers aG)
  have haX : aG ∈ Cb := hUb haU
  have hcX : c ∈ Cb := hUb hcU
  have hpa := conj_pair_images hLcomp hLxcomp hLchar
    (image_centralizes (P := P) (y := ⟨aG, haX⟩) (hUP haU))
  have hpc := conj_pair_images hLcomp hLxcomp hLchar
    (image_centralizes (P := P) (y := ⟨c, hcX⟩) (hUP hcU))
  by_cases hfa : L.map (MulAut.conj (π ⟨aG, haX⟩)).toMonoidHom = L
  · exact false_of_isComponent_fixed hPb haX (hU2 aG haU) (hUc aG haU ha1).1
      (hUc aG haU ha1).2 hLcomp hLne hLchar hfa
  · have hpa_swap : L.map (MulAut.conj (π ⟨aG, haX⟩)).toMonoidHom = Lx := hpa.1.resolve_left hfa
    by_cases hfc : L.map (MulAut.conj (π ⟨c, hcX⟩)).toMonoidHom = L
    · exact false_of_isComponent_fixed hPb hcX (hU2 c hcU) (hUc c hcU hc1).1
        (hUc c hcU hc1).2 hLcomp hLne hLchar hfc
    · have hpc_swap : L.map (MulAut.conj (π ⟨c, hcX⟩)).toMonoidHom = Lx := hpc.1.resolve_left hfc
      have hacU : aG * c ∈ U := U.mul_mem haU hcU
      have hac1 : aG * c ≠ 1 := by
        intro h'
        apply hca
        have h1 : c = aG⁻¹ := (inv_eq_of_mul_eq_one_right h').symm
        have h2 : aG⁻¹ = aG := inv_eq_of_mul_eq_one_right (hU2 aG haU)
        rw [h1, h2]
      have hacX : aG * c ∈ Cb := hUb hacU
      have hac2 : (aG * c) * (aG * c) = 1 := hU2 (aG * c) hacU
      have hvfix : L.map (MulAut.conj (π ⟨aG * c, hacX⟩)).toMonoidHom = L := by
        have hprod : (⟨aG * c, hacX⟩ : ↥Cb) = ⟨aG, haX⟩ * ⟨c, hcX⟩ := rfl
        rw [hprod, map_mul, map_mul MulAut.conj, map_mulAut_mul, hpc_swap]
        exact hpa.2.resolve_right fun hcon =>
          hLM (Subgroup.map_injective (f := (MulAut.conj (π ⟨aG, haX⟩)).toMonoidHom)
            (MulAut.conj (π ⟨aG, haX⟩)).injective (hpa_swap.trans hcon.symm))
      exact false_of_isComponent_fixed hPb hacX hac2 (hUc (aG * c) hacU hac1).1
        (hUc (aG * c) hacU hac1).2 hLcomp hLne hLchar hvfix

end CFSG.ComponentClassification.GrSLit.L34Sec5S
