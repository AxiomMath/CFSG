module

public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation
public import CFSG.LieType.Chevalley.LangWeylInvolutionReflections

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k]

theorem monomial_inverted_root_SL2_rotation (hk : ringChar k ≠ 2) {n : ModGL τ k}
    (hn : n ∈ monomialSubgroup τ k) (hn2 : n ^ 2 = 1) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hwβ : weylQuotientHom τ k ⟨n, hn⟩ • β = -β) :
    ∃ y ∈ rootRankOneGroup τ k β, ∃ hyn : y * n * y⁻¹ ∈ monomialSubgroup τ k,
      weylQuotientHom τ k ⟨_, hyn⟩ = rootReflection β * weylQuotientHom τ k ⟨n, hn⟩ := by
  classical
  set w := weylQuotientHom τ k ⟨n, hn⟩ with hw
  set ι := rootSL2 τ k β with hι
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have hinj : Function.Injective ι := fun B B' h =>
    simpleRootSL2_injective hk _ (by simpa [hι, rootSL2_apply] using h)
  have hA : ∀ γ, IsRoot τ γ → ∃ μ : kˣ, ∀ c : k,
      n * pinnedX τ k γ c * n⁻¹ = pinnedX τ k (w • γ) (μ * c) := by
    intro γ hγ
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn hγ
    exact ⟨μ, by simpa [hw] using hμ⟩
  set s₀ : kˣ := if (pinnedData τ β).2.2 = 1 then 1 else -1 with hs₀
  have hs₀z : ∀ z : k, (pinnedData τ β).2.2 • z = (s₀ : k) * z := by
    intro z
    rcases pinnedSign_eq τ β with h | h <;> simp [hs₀, h]
  have hs₀sq : s₀ * s₀ = 1 := by
    rcases pinnedSign_eq τ β with h | h <;> simp [hs₀, h]
  have hu : ∀ z, ι (uSL z) = pinnedX τ k β ((s₀ : k) * z) := fun z => by
    rw [hι, rootSL2_uSL_eq, hs₀z]
  obtain ⟨ε₁, hε₁, hl⟩ := exists_rootSL2_vSL_eq (K := k) hβ
  set s₁ : kˣ := Units.mkOfMulEqOne ε₁ ε₁ hε₁ with hs₁
  have hs₁sq : s₁ * s₁ = 1 := Units.ext (by simpa [hs₁] using hε₁)
  have hl' : ∀ z, ι (vSL z) = pinnedX τ k (-β) ((s₁ : k) * z) := hl
  have hωneg : w • (-β) = β := by
    rw [smul_neg, hwβ, neg_neg]
  obtain ⟨μ₁, hμ₁⟩ := hA β hβ
  obtain ⟨μ₂, hμ₂⟩ := hA (-β) (IsRoot.neg hβ)
  set a : kˣ := s₁ * μ₁ * s₀ with ha
  set b : kˣ := s₀ * μ₂ * s₁ with hb
  have hAu : ∀ z, n * ι (uSL z) * n⁻¹ = ι (vSL ((a : k) * z)) := fun z => by
    rw [hu, hμ₁, hwβ, hl', ha]
    congr 1
    calc (μ₁ : k) * ((s₀ : k) * z) = ((s₁ * s₁ : kˣ) : k) * (μ₁ * (s₀ * z)) := by
          rw [hs₁sq, Units.val_one, one_mul]
      _ = _ := by push_cast; ring
  have hAl : ∀ z, n * ι (vSL z) * n⁻¹ = ι (uSL ((b : k) * z)) := fun z => by
    rw [hl', hμ₂, hωneg, hu, hb]
    congr 1
    calc (μ₂ : k) * ((s₁ : k) * z) = ((s₀ * s₀ : kˣ) : k) * (μ₂ * (s₁ * z)) := by
          rw [hs₀sq, Units.val_one, one_mul]
      _ = _ := by push_cast; ring
  have hAA : n * n = 1 := by rw [← sq]; exact hn2
  have hAinv : n⁻¹ = n := inv_eq_of_mul_eq_one_right hAA
  have hba : b * a = 1 := by
    have h1 : ι (uSL 1) = ι (uSL ((b : k) * (a : k))) := by
      calc ι (uSL 1) = n * (n * ι (uSL 1) * n⁻¹) * n⁻¹ := by
            rw [hAinv]
            calc ι (uSL 1) = (n * n) * ι (uSL 1) * (n * n) := by rw [hAA, one_mul, mul_one]
              _ = _ := by group
        _ = ι (uSL ((b : k) * (a : k))) := by rw [hAu, mul_one, hAl]
    have h2' := congrArg (fun M : SL2 k => (M : Matrix (Fin 2) (Fin 2) k) 0 1) (hinj h1)
    simp only [uSL] at h2'
    exact Units.ext (by
      rw [Units.val_mul, Units.val_one]
      simpa using h2'.symm)
  obtain ⟨c₀, hc₀⟩ := IsAlgClosed.exists_pow_nat_eq (-((a⁻¹ : kˣ) : k)) (n := 2) (by norm_num)
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, neg_eq_zero] at hc₀
    exact (a⁻¹).ne_zero hc₀
  set c : kˣ := Units.mk0 c₀ hc₀0 with hc
  set r := rootWeylSL2 τ k β c with hr
  have hru : ∀ z, r * ι (uSL z) * r⁻¹ = ι (vSL ((a : k) * z)) := fun z => by
    rw [hr, rootWeylSL2, ← map_inv, ← map_mul, ← map_mul, nSL_mul_uSL, mul_inv_cancel_right]
    congr 2
    have e : ((c⁻¹ : kˣ) : k) ^ 2 = ((a : kˣ) : k) * -1 := by
      rw [Units.val_inv_eq_inv_val, inv_pow, hc, Units.val_mk0, hc₀, Units.val_inv_eq_inv_val,
        inv_neg, inv_inv, mul_neg_one]
    rw [e]
    ring
  have hrl : ∀ z, r * ι (vSL z) * r⁻¹ = ι (uSL ((b : k) * z)) := fun z => by
    rw [hr, rootWeylSL2, ← map_inv, ← map_mul, ← map_mul, nSL_mul_vSL, mul_inv_cancel_right]
    congr 2
    have hb' : (b : k) = ((a⁻¹ : kˣ) : k) := by
      rw [eq_inv_of_mul_eq_one_left hba]
    rw [hc, Units.val_mk0, hc₀, hb']
    ring
  set η := r⁻¹ * n with hη
  have hηu : ∀ z, η * ι (uSL z) * η⁻¹ = ι (uSL z) := fun z => by
    have e := hru z
    calc η * ι (uSL z) * η⁻¹ = r⁻¹ * (n * ι (uSL z) * n⁻¹) * r := by rw [hη]; group
      _ = r⁻¹ * (r * ι (uSL z) * r⁻¹) * r := by rw [hAu, e]
      _ = ι (uSL z) := by group
  have hηl : ∀ z, η * ι (vSL z) * η⁻¹ = ι (vSL z) := fun z => by
    have e := hrl z
    calc η * ι (vSL z) * η⁻¹ = r⁻¹ * (n * ι (vSL z) * n⁻¹) * r := by rw [hη]; group
      _ = r⁻¹ * (r * ι (vSL z) * r⁻¹) * r := by rw [hAl, e]
      _ = ι (vSL z) := by group
  have hηall : ∀ B : SL2 k, η * ι B * η⁻¹ = ι B := by
    have heq : (MulAut.conj η).toMonoidHom.comp ι = ι :=
      MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
        rcases hg with ⟨z, rfl⟩ | ⟨z, rfl⟩
        · exact hηu z
        · exact hηl z
    intro B
    exact congrArg (fun f : SL2 k →* ModGL τ k => f B) heq
  obtain ⟨ζ₀, hζ₀⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : k) (n := 2) (by norm_num)
  have hζ₀0 : ζ₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, neg_eq_zero] at hζ₀
    exact one_ne_zero hζ₀
  set ζ : kˣ := Units.mk0 ζ₀ hζ₀0 with hζ
  have hζsq : (ζ : k) ^ 2 = -1 := by rw [hζ, Units.val_mk0, hζ₀]
  set Q := qSL c ζ h2 with hQ
  set y := ι Q⁻¹ with hy
  have hyr : y * r * y⁻¹ = rootTorusSL2 τ k β ζ := by
    have e : Q⁻¹ * nSL c * Q = HSL ζ := by
      rw [mul_assoc, hQ, nSL_mul_qSL c ζ h2 hζsq, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hy, hr, rootWeylSL2, ← map_inv, inv_inv, ← map_mul, ← map_mul, e, rootTorusSL2]
  have hyη : y * η * y⁻¹ = η := by
    have e := hηall Q⁻¹
    rw [← hy] at e
    calc y * η * y⁻¹ = y * (η * y⁻¹ * η⁻¹) * η := by group
      _ = y * (η * y * η⁻¹)⁻¹ * η := by group
      _ = η := by rw [e]; group
  have hdH : ∀ c : kˣ, rootTorusSL2 τ k β c ∈ torusGroup τ k :=
    (exceptional_Lang_root_rank_one_torus_transport τ k hβ).2.1
  have hrN : ∀ c : kˣ, ∃ h : rootWeylSL2 τ k β c ∈ monomialSubgroup τ k,
      weylQuotientHom τ k ⟨_, h⟩ = rootReflection β :=
    (exceptional_Lang_root_rank_one_torus_transport τ k hβ).2.2.1
  obtain ⟨hrM, hrπ⟩ := hrN c
  have hdM : rootTorusSL2 τ k β ζ ∈ monomialSubgroup τ k :=
    Subgroup.mem_sup_left (hdH ζ)
  set n₁ := rootTorusSL2 τ k β ζ * r⁻¹ * n with hn₁def
  have hn₁ : n₁ ∈ monomialSubgroup τ k := mul_mem (mul_mem hdM (inv_mem hrM)) hn
  have hy_eq : y * n * y⁻¹ = n₁ := by
    calc y * n * y⁻¹ = y * (r * η) * y⁻¹ := by rw [hη]; group
      _ = (y * r * y⁻¹) * (y * η * y⁻¹) := by group
      _ = rootTorusSL2 τ k β ζ * η := by rw [hyr, hyη]
      _ = rootTorusSL2 τ k β ζ * (r⁻¹ * n) := by rw [hη]
      _ = n₁ := by rw [hn₁def]; group
  have hyn : y * n * y⁻¹ ∈ monomialSubgroup τ k := by
    rw [hy_eq]
    exact hn₁
  refine ⟨y, ⟨Q⁻¹, rfl⟩, hyn, ?_⟩
  have hquot : weylQuotientHom τ k ⟨y * n * y⁻¹, hyn⟩ =
      weylQuotientHom τ k ⟨n₁, hn₁⟩ :=
    congrArg (weylQuotientHom τ k) (Subtype.ext hy_eq)
  rw [hquot]
  have hsplit : (⟨n₁, hn₁⟩ : monomialSubgroup τ k) =
      ⟨_, hdM⟩ * (⟨r, hrM⟩ : monomialSubgroup τ k)⁻¹ * ⟨n, hn⟩ := rfl
  have hdπ : weylQuotientHom τ k ⟨_, hdM⟩ = 1 :=
    weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup (hdH ζ))
  rw [hsplit, map_mul, map_mul, map_inv, hdπ, hrπ, one_mul, rootReflection_inv hβ]

private def invertedRootFinset {τ : Tag} {k : Type} [Field k]
    (a : Fin τ.rank → kˣ) (w : WeylGroup τ) : Finset (Fin τ.rank → ℤ) := by
  classical
  exact (rootFinset τ).filter fun α => rootChar a α = 1 ∧ w • α = -α

private theorem mem_invertedRootFinset {τ : Tag} {k : Type} [Field k]
    (a : Fin τ.rank → kˣ) (w : WeylGroup τ) {α : Fin τ.rank → ℤ} :
    α ∈ invertedRootFinset a w ↔ IsRoot τ α ∧ rootChar a α = 1 ∧ w • α = -α := by
  simp [invertedRootFinset, mem_rootFinset]

private theorem exists_conj_aux (hk : ringChar k ≠ 2) (a : Fin τ.rank → kˣ) (N : ℕ) :
    ∀ (n : ModGL τ k) (hn : n ∈ monomialSubgroup τ k), n ^ 2 = 1 →
      (invertedRootFinset a (weylQuotientHom τ k ⟨n, hn⟩)).card ≤ N →
      ∃ g ∈ adjointGroup τ k, rootDiagUnit τ a * g = g * rootDiagUnit τ a ∧
        ∃ hgn : g * n * g⁻¹ ∈ monomialSubgroup τ k,
          ∀ α, IsRoot τ α → rootChar a α = 1 →
            weylQuotientHom τ k ⟨_, hgn⟩ • α ≠ -α := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro n hn hn2 hN
    classical
    by_cases hne : invertedRootFinset a (weylQuotientHom τ k ⟨n, hn⟩) = ∅
    · refine ⟨1, one_mem _, ?_, ?_⟩
      · group
      · have hmn : (1 : ModGL τ k) * n * 1⁻¹ ∈ monomialSubgroup τ k := by
          simpa using hn
        refine ⟨hmn, ?_⟩
        intro α hα hχα hinv
        have hinv' : weylQuotientHom τ k ⟨n, hn⟩ • α = -α := by
          simpa using hinv
        have hmem : α ∈ invertedRootFinset a (weylQuotientHom τ k ⟨n, hn⟩) := by
          rw [mem_invertedRootFinset]
          exact ⟨hα, hχα, hinv'⟩
        rw [hne] at hmem
        exact absurd hmem (Finset.notMem_empty α)
    · obtain ⟨β, hβmem⟩ := Finset.nonempty_iff_ne_empty.2 hne
      rw [mem_invertedRootFinset] at hβmem
      obtain ⟨hβ, hχβ, hwβ⟩ := hβmem
      obtain ⟨y, hyL, hyn, hπ⟩ := monomial_inverted_root_SL2_rotation hk hn hn2 hβ hwβ
      set w := weylQuotientHom τ k ⟨n, hn⟩ with hw
      have hwβ' : w • β = -β := by simpa [hw] using hwβ
      set n' := y * n * y⁻¹ with hn'def
      have hn'N : n' ∈ monomialSubgroup τ k := by
        rw [hn'def]
        exact hyn
      have hn'2 : n' ^ 2 = 1 := by
        rw [hn'def, sq]
        have hnn : n * n = 1 := by simpa [sq] using hn2
        calc y * n * y⁻¹ * (y * n * y⁻¹) = y * (n * n) * y⁻¹ := by group
          _ = 1 := by rw [hnn]; group
      have hπ' : weylQuotientHom τ k ⟨n', hn'N⟩ = rootReflection β * w := by
        have hsubst : (⟨n', hn'N⟩ : monomialSubgroup τ k) =
            ⟨y * n * y⁻¹, hyn⟩ := Subtype.ext hn'def
        rw [hsubst]
        simpa [hw] using hπ
      have hww : ∀ v : Fin τ.rank → ℤ, w • (w • v) = v := by
        have hw2 : w * w = 1 := by
          have e : (⟨n, hn⟩ * ⟨n, hn⟩ : monomialSubgroup τ k) = 1 :=
            Subtype.ext (by simpa [sq] using hn2)
          have h := congrArg (weylQuotientHom τ k) e
          rw [map_mul, map_one] at h
          simpa [hw] using h
        intro v
        rw [← mul_smul, hw2, one_smul]
      have hsub : invertedRootFinset a (weylQuotientHom τ k ⟨n', hn'N⟩) ⊆
          invertedRootFinset a w := by
        intro γ hγ
        rw [mem_invertedRootFinset] at hγ ⊢
        obtain ⟨hγroot, hχγ, hγinv⟩ := hγ
        have hγeq : (rootReflection β * w) • γ = -γ := by
          rw [← hπ']
          exact hγinv
        obtain ⟨hwγ, -, -⟩ :=
          invertedRoots_reflection_subset_general hww hβ hwβ' hγeq
        exact ⟨hγroot, hχγ, hwγ⟩
      have hβF : β ∈ invertedRootFinset a w := by
        rw [mem_invertedRootFinset]
        exact ⟨hβ, hχβ, hwβ'⟩
      have hβnot : β ∉ invertedRootFinset a (weylQuotientHom τ k ⟨n', hn'N⟩) := by
        intro hmem
        rw [mem_invertedRootFinset] at hmem
        obtain ⟨-, -, hβinv⟩ := hmem
        have hπβ : weylQuotientHom τ k ⟨n', hn'N⟩ • β = β := by
          rw [hπ', mul_smul, hwβ', smul_neg, rootReflection_smul_self hβ, neg_neg]
        have hzero : β = 0 := by
          have h : β = -β := by
            calc β = weylQuotientHom τ k ⟨n', hn'N⟩ • β := hπβ.symm
              _ = -β := hβinv
          funext j
          have h' : β j = -β j := by simpa using congrFun h j
          simp only [Pi.zero_apply]
          linarith
        exact hβ.ne_zero hzero
      have hssub : invertedRootFinset a (weylQuotientHom τ k ⟨n', hn'N⟩) ⊂
          invertedRootFinset a w := by
        refine Finset.ssubset_iff_subset_ne.2 ⟨hsub, ?_⟩
        rintro heq
        have hmem : β ∈ invertedRootFinset a (weylQuotientHom τ k ⟨n', hn'N⟩) := by
          rw [heq]
          exact hβF
        exact hβnot hmem
      have hlt : (invertedRootFinset a (weylQuotientHom τ k ⟨n', hn'N⟩)).card <
          (invertedRootFinset a w).card := Finset.card_lt_card hssub
      have hltN : (invertedRootFinset a (weylQuotientHom τ k ⟨n', hn'N⟩)).card < N :=
        lt_of_lt_of_le hlt hN
      obtain ⟨g', hg'C, hg'a, hgn', hgood'⟩ :=
        ih _ hltN n' hn'N hn'2 le_rfl
      have hyC : y ∈ adjointGroup τ k :=
        (exceptional_Lang_root_rank_one_data τ k β).2.2.2.2.2.1 hyL
      have hdaY : rootDiagUnit τ a * y = y * rootDiagUnit τ a := by
        have hprod : (∏ i, a i ^ β i) = 1 := by
          simpa [rootChar] using hχβ
        exact (exceptional_Lang_root_rank_one_torus_transport τ k hβ).2.2.2.2.2.2.2
          a hprod y hyL
      refine ⟨g' * y, mul_mem hg'C hyC, ?_, ?_⟩
      · calc rootDiagUnit τ a * (g' * y) = (rootDiagUnit τ a * g') * y := by group
          _ = (g' * rootDiagUnit τ a) * y := by rw [hg'a]
          _ = g' * (rootDiagUnit τ a * y) := by group
          _ = g' * (y * rootDiagUnit τ a) := by rw [hdaY]
          _ = g' * y * rootDiagUnit τ a := by group
      · have hconj : (g' * y) * n * (g' * y)⁻¹ = g' * n' * g'⁻¹ := by
          rw [hn'def]
          group
        have hgn : (g' * y) * n * (g' * y)⁻¹ ∈ monomialSubgroup τ k := by
          rw [hconj]
          exact hgn'
        refine ⟨hgn, ?_⟩
        have hquot : weylQuotientHom τ k ⟨(g' * y) * n * (g' * y)⁻¹, hgn⟩ =
            weylQuotientHom τ k ⟨g' * n' * g'⁻¹, hgn'⟩ :=
          congrArg (weylQuotientHom τ k) (Subtype.ext hconj)
        rw [hquot]
        exact hgood'

theorem exists_conj_monomial_no_inverted_root (hk : ringChar k ≠ 2) (a : Fin τ.rank → kˣ)
    {n : ModGL τ k} (hn : n ∈ monomialSubgroup τ k) (hn2 : n ^ 2 = 1) :
    ∃ g ∈ adjointGroup τ k, rootDiagUnit τ a * g = g * rootDiagUnit τ a ∧
      ∃ hgn : g * n * g⁻¹ ∈ monomialSubgroup τ k,
        ∀ α, IsRoot τ α → rootChar a α = 1 → weylQuotientHom τ k ⟨_, hgn⟩ • α ≠ -α := by
  classical
  exact exists_conj_aux hk a
    (invertedRootFinset a (weylQuotientHom τ k ⟨n, hn⟩)).card n hn hn2 le_rfl

end CFSG.LieType.Chevalley
