module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95UBasis
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClU4Core

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup Module Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.CentralQuotientLift
open CFSG.ComponentClassification.OddClassSelector
open CFSG.GH74.GLS.IVK
open CFSG.ComponentClassification.CatalogueBUnitaryB (projSpecial fixedSubgroup_conj sesqNormOneScalars_le_center)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section DLevel

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]
  {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E}

theorem paired_false (hp : p ≠ 2) [FiniteDimensional E V] (hn : finrank E V = 4)
    {T : sesqUnitaryGroup B} {l : E} (hl0 : l ≠ 0) (hN : h.norm l = -1)
    (h2m : 2 * finrank E (eigenPlus l (unitaryOp T)) = finrank E V)
    (e : centralizer ({T} : Set (sesqUnitaryGroup B)) ≃*
      LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp T)))
    (hecompat : ∀ g : centralizer ({T} : Set (sesqUnitaryGroup B)),
      (eigenPlus l (unitaryOp T)).subtype ∘ₗ
          ((e g : LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp T))) :
            Module.End E (eigenPlus l (unitaryOp T))) =
        unitaryOp (g : sesqUnitaryGroup B) ∘ₗ (eigenPlus l (unitaryOp T)).subtype)
    {Y : Subgroup (sesqUnitaryGroup B)}
    (hY : CFSG.Assembly.IsComponentOf Y (centralizer ({T} : Set (sesqUnitaryGroup B))))
    {y : sesqUnitaryGroup B} (hyY : y ∈ Y)
    (hyT : (QuotientGroup.mk y : sesqProjUnitary h B) = QuotientGroup.mk T) : False := by
  classical
  obtain ⟨c, hc, hTc⟩ := exists_scalar_of_mk_eq hyT
  have hc0 : c ≠ 0 := ne_zero_of_norm_eq_one h hc
  have hyC : y ∈ centralizer ({T} : Set (sesqUnitaryGroup B)) := hY.1 hyY
  let y' : centralizer ({T} : Set (sesqUnitaryGroup B)) := ⟨y, hyC⟩
  have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hY.1).mp hY
  have hperf : Group.IsPerfect (Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B)))) :=
    hY₁.1.1
  have hL := Subgroup.isPerfect_iff.mp hperf
  let d : centralizer ({T} : Set (sesqUnitaryGroup B)) →* (E)ˣ :=
    (Units.map (LinearMap.det : Module.End E (eigenPlus l (unitaryOp T)) →* E)).comp e.toMonoidHom
  have hd : d y' = 1 := by
    have hmem : y' ∈ Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B))) := hyY
    rw [← hL] at hmem
    have hle : ⁅Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B))),
        Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup B)))⁆ ≤ d.ker := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      simp [commutatorElement_def]
    exact hle hmem
  have hscal : ((e y' : LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp T))) :
      Module.End E (eigenPlus l (unitaryOp T))) = (c⁻¹ * l) • 1 := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    have h1 := LinearMap.congr_fun (hecompat y') v
    have h2 := hTc (v : V)
    rw [(mem_eigenPlus_iff' hl0).1 v.2] at h2
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1]
    change unitaryOp y (v : V) = (c⁻¹ * l) • (v : V)
    rw [mul_smul, h2, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hdet : (c⁻¹ * l) ^ 2 = 1 := by
    have h1 : LinearMap.det ((e y' : LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp T))) :
      Module.End E (eigenPlus l (unitaryOp T))) = 1 := by
      have := congrArg (fun u : Eˣ => (u : E)) hd
      simpa [d] using this
    rw [hscal, LinearMap.det_smul, map_one, mul_one, show finrank E
      (eigenPlus l (unitaryOp T)) = 2 by omega] at h1
    exact h1
  have h2 := two_ne_zero_of_odd h hp
  have hne : (1 : E) ≠ -1 := by
    intro h1
    apply h2
    linear_combination h1
  have hcinv : h.norm c⁻¹ = 1 := by
    have := norm_mul_eq' h c c⁻¹
    rw [mul_inv_cancel₀ hc0, hc, one_mul] at this
    have h3 : h.norm 1 = 1 := by simp [UnitaryFieldData.norm]
    rw [h3] at this
    exact this.symm
  have hnorm : h.norm (c⁻¹ * l) = -1 := by rw [norm_mul_eq', hcinv, hN, one_mul]
  have h1n : h.norm 1 = 1 := by simp [UnitaryFieldData.norm]
  rw [sq] at hdet
  rcases mul_self_eq_one_iff.1 hdet with h3 | h3
  · rw [h3, h1n] at hnorm
    exact hne hnorm
  · rw [h3, norm_neg', h1n] at hnorm
    exact hne hnorm


theorem split_false (hp : p ≠ 2) [FiniteDimensional E V] (hB : B.IsSymm)
    {A W : Submodule E V} (hc : IsCompl A W) (horth : ∀ a ∈ A, ∀ w ∈ W, B a w = 0)
    (hsepA : (B.domRestrict₁₂ A A).SeparatingLeft) (hsepW : (B.domRestrict₁₂ W W).SeparatingLeft)
    {T : sesqUnitaryGroup B} {μ : E} (hμ : μ ≠ 0)
    (hTA : ∀ a ∈ A, unitaryOp T a = μ • a) (hTW : ∀ w ∈ W, unitaryOp T w = -(μ • w))
    (hA2 : 2 ≤ finrank E A) (hW1 : 1 ≤ finrank E W)
    (hdim : finrank E A + finrank E W = 4 ∨ finrank E A + finrank E W = 5)
    {K' : Subgroup (sesqProjUnitary h B)}
    (hKset : ∀ x, x ∈ K' ↔ ∃ g ∈ summandUnitarySet B A W,
      (QuotientGroup.mk g : sesqProjUnitary h B) = x)
    (huniq : ∀ v ∈ K', v * v = 1 → v = 1 ∨ v = QuotientGroup.mk T)
    (hconj : ∀ d ∈ projSpecial h B, d * QuotientGroup.mk T = QuotientGroup.mk T * d →
      ∀ k ∈ K', d * k * d⁻¹ ∈ K')
    (hinv2 : ∀ a b : sesqProjUnitary h B, a ∈ projSpecial h B → b ∈ projSpecial h B →
      a * a = 1 → b * b = 1 → a * b = b * a → a ≠ 1 → b ≠ 1 → a ≠ b →
      (∀ k ∈ K', a * k = k * a) → (∀ k ∈ K', b * k = k * b) → False)
    (hnab : ∃ k₁ ∈ K', ∃ k₂ ∈ K', k₁ * k₂ ≠ k₂ * k₁) : False := by
  classical
  have h2 := two_ne_zero_of_odd h hp
  obtain ⟨Q⟩ := exists_adaptedONB (h := h) hB hsepA hsepW
  have hG := Q.gram hc hB horth
  have hbA : ∀ i, Q.b hc (Sum.inl i) ∈ A := fun i => by
    rw [AdaptedONB.b_inl]; exact (Q.ea i).2
  have hbW : ∀ j, Q.b hc (Sum.inr j) ∈ W := fun j => by
    rw [AdaptedONB.b_inr]; exact (Q.ew j).2
  by_cases h3 : 3 ≤ finrank E A
  ·
    let i0 : Fin (finrank E A) := ⟨0, by omega⟩
    let i1 : Fin (finrank E A) := ⟨1, by omega⟩
    let i2 : Fin (finrank E A) := ⟨2, by omega⟩
    have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
    have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
    have hS : Even ({i0, i1} : Finset (Fin (finrank E A))).card := by
      rw [Finset.card_pair h01]; exact even_two
    set x := signU (Q.b hc) hG (({i0, i1} : Finset (Fin (finrank E A))).map Function.Embedding.inl)
      with hx
    have hxK : (QuotientGroup.mk x : sesqProjUnitary h B) ∈ K' :=
      (hKset _).2 ⟨x, Q.signU_A_mem hc hG _ hS, rfl⟩
    have hi : (Sum.inl i0 : Fin (finrank E A) ⊕ Fin (finrank E W)) ∈
        ({i0, i1} : Finset (Fin (finrank E A))).map Function.Embedding.inl := by simp
    have hj : (Sum.inl i2 : Fin (finrank E A) ⊕ Fin (finrank E W)) ∉
        ({i0, i1} : Finset (Fin (finrank E A))).map Function.Embedding.inl := by
      simp [h02.symm, h12.symm]
    rcases huniq _ hxK (mk_signU_mul_self _ hG _) with h1 | h1
    · exact mk_signU_ne_one (Q.b hc) hG h2 hi hj h1
    · exact mk_signU_ne_mk (Q.b hc) hG h2 hi hj hμ (hTA _ (hbA i0)) (hTA _ (hbA i2)) h1
  · have hA2' : finrank E A = 2 := by omega
    by_cases hW3 : 3 ≤ finrank E W
    ·
      let j0 : Fin (finrank E W) := ⟨0, by omega⟩
      let j1 : Fin (finrank E W) := ⟨1, by omega⟩
      let j2 : Fin (finrank E W) := ⟨2, by omega⟩
      let i0 : Fin (finrank E A) := ⟨0, by omega⟩
      have h01 : j0 ≠ j1 := by simp [j0, j1, Fin.ext_iff]
      have h02 : j0 ≠ j2 := by simp [j0, j2, Fin.ext_iff]
      have h12 : j1 ≠ j2 := by simp [j1, j2, Fin.ext_iff]
      have hS1 : Even ({j0, j1} : Finset (Fin (finrank E W))).card := by
        rw [Finset.card_pair h01]; exact even_two
      have hS2 : Even ({j0, j2} : Finset (Fin (finrank E W))).card := by
        rw [Finset.card_pair h02]; exact even_two
      set a := signU (Q.b hc) hG (({j0, j1} : Finset (Fin (finrank E W))).map Function.Embedding.inr)
        with ha
      set b' := signU (Q.b hc) hG (({j0, j2} : Finset (Fin (finrank E W))).map Function.Embedding.inr)
        with hb'
      have hia : (Sum.inr j0 : Fin (finrank E A) ⊕ Fin (finrank E W)) ∈
          ({j0, j1} : Finset (Fin (finrank E W))).map Function.Embedding.inr := by simp
      have hib : (Sum.inr j0 : Fin (finrank E A) ⊕ Fin (finrank E W)) ∈
          ({j0, j2} : Finset (Fin (finrank E W))).map Function.Embedding.inr := by simp
      have hja : (Sum.inl i0 : Fin (finrank E A) ⊕ Fin (finrank E W)) ∉
          ({j0, j1} : Finset (Fin (finrank E W))).map Function.Embedding.inr := by simp
      have hjb : (Sum.inl i0 : Fin (finrank E A) ⊕ Fin (finrank E W)) ∉
          ({j0, j2} : Finset (Fin (finrank E W))).map Function.Embedding.inr := by simp
      have hj1 : (Sum.inr j1 : Fin (finrank E A) ⊕ Fin (finrank E W)) ∈
          ({j0, j1} : Finset (Fin (finrank E W))).map Function.Embedding.inr := by simp
      have hj1' : (Sum.inr j1 : Fin (finrank E A) ⊕ Fin (finrank E W)) ∉
          ({j0, j2} : Finset (Fin (finrank E W))).map Function.Embedding.inr := by
        simp [h01.symm, h12]
      have hcent : ∀ (S : Finset (Fin (finrank E W))) (k : sesqProjUnitary h B), k ∈ K' →
          (QuotientGroup.mk (signU (Q.b hc) hG (S.map Function.Embedding.inr)) :
            sesqProjUnitary h B) * k =
          k * QuotientGroup.mk (signU (Q.b hc) hG (S.map Function.Embedding.inr)) := by
        intro S k hk
        obtain ⟨g, hg, rfl⟩ := (hKset k).1 hk
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Q.signU_W_commute hc hG hg S).symm]
      refine hinv2 (QuotientGroup.mk a) (QuotientGroup.mk b')
        (mk_signU_mem_projSpecial _ hG (by rw [Finset.card_map]; exact hS1))
        (mk_signU_mem_projSpecial _ hG (by rw [Finset.card_map]; exact hS2))
        (mk_signU_mul_self _ hG _) (mk_signU_mul_self _ hG _) ?_
        (mk_signU_ne_one (Q.b hc) hG h2 hia hja) (mk_signU_ne_one (Q.b hc) hG h2 hib hjb)
        (mk_signU_ne_mk_signU (Q.b hc) hG h2 hj1 hj1' hja hjb)
        (fun k hk => hcent _ k hk) (fun k hk => hcent _ k hk)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, signU_comm]
    ·
      have hW2 : finrank E W = 2 := by omega
      have hAW : finrank E A = finrank E W := by omega
      obtain ⟨s, hsA, hsW, hdet, hsT⟩ := Q.exists_swap hc hG hAW (by omega) hTA hTW
      have hsproj : (QuotientGroup.mk s : sesqProjUnitary h B) ∈ projSpecial h B := by
        refine Subgroup.mem_map_of_mem (QuotientGroup.mk' (sesqNormOneScalars h B)) ?_
        rw [CFSG.ComponentClassification.CatalogueBUnitaryB.mem_unitarySpecial]
        exact hdet
      have hcomm : (QuotientGroup.mk s : sesqProjUnitary h B) * QuotientGroup.mk T =
          QuotientGroup.mk T * QuotientGroup.mk s := by
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        refine mk_eq_of_smul (c := -1) ?_ fun v => ?_
        · simp [UnitaryFieldData.norm]
        · have := LinearMap.congr_fun hsT v
          simp only [Module.End.mul_apply, LinearMap.neg_apply] at this
          show unitaryOp T (unitaryOp s v) = (-1 : E) • unitaryOp s (unitaryOp T v)
          rw [this]
          simp
      obtain ⟨hsiA, hsiW⟩ := swap_inv hc hsA hsW
      have hcentral : ∀ g ∈ summandUnitarySet B A W, ∀ k ∈ K',
          (QuotientGroup.mk (s * g * s⁻¹) : sesqProjUnitary h B) * k =
            k * QuotientGroup.mk (s * g * s⁻¹) := by
        intro g hg k hk
        obtain ⟨g₂, hg₂, rfl⟩ := (hKset k).1 hk
        obtain ⟨hgW, hgA, -⟩ := hg
        obtain ⟨hg₂W, hg₂A, -⟩ := hg₂
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        refine summand_commute hc hg₂W hg₂A (fun a ha => ?_) (fun w hw => ?_) |>.symm
        · show unitaryOp s (unitaryOp g (unitaryOp s⁻¹ a)) = a
          rw [hgW _ (hsiA a ha), unitaryOp_apply_inv]
        · show unitaryOp s (unitaryOp g (unitaryOp s⁻¹ w)) ∈ W
          exact hsA _ (hgA _ (hsiW w hw))
      obtain ⟨k₁, hk₁, k₂, hk₂, hne⟩ := hnab
      apply hne
      set ms : sesqProjUnitary h B := QuotientGroup.mk s with hms
      obtain ⟨g₁, hg₁, rfl⟩ := (hKset k₁).1 hk₁
      have hk₂' : ms * k₂ * ms⁻¹ ∈ K' := hconj ms hsproj hcomm k₂ hk₂
      have hcen := hcentral g₁ hg₁ _ hk₂'
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hcen
      calc (QuotientGroup.mk g₁ : sesqProjUnitary h B) * k₂
          = ms⁻¹ * ((ms * QuotientGroup.mk g₁ * ms⁻¹) * (ms * k₂ * ms⁻¹)) * ms := by group
        _ = ms⁻¹ * ((ms * k₂ * ms⁻¹) * (ms * QuotientGroup.mk g₁ * ms⁻¹)) * ms := by rw [hcen]
        _ = k₂ * QuotientGroup.mk g₁ := by group


theorem ivk95_unitary_false (hp : p ≠ 2) [FiniteDimensional E V] [Finite (sesqUnitaryGroup B)]
    (hdim : finrank E V = 4 ∨ finrank E V = 5) (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {T : sesqUnitaryGroup B} (hT : orderOf (QuotientGroup.mk T : sesqProjUnitary h B) = 2)
    {K' : Subgroup (sesqProjUnitary h B)}
    (hK : CFSG.Assembly.IsComponentOf K'
      (fixedSubgroup (MulAut.conj (QuotientGroup.mk' (sesqNormOneScalars h B) T))))
    (hmem : (QuotientGroup.mk T : sesqProjUnitary h B) ∈ K')
    (huniq : ∀ v ∈ K', v * v = 1 → v = 1 ∨ v = QuotientGroup.mk T)
    (hconj : ∀ d ∈ projSpecial h B, d * QuotientGroup.mk T = QuotientGroup.mk T * d →
      ∀ k ∈ K', d * k * d⁻¹ ∈ K')
    (hinv2 : ∀ a b : sesqProjUnitary h B, a ∈ projSpecial h B → b ∈ projSpecial h B →
      a * a = 1 → b * b = 1 → a * b = b * a → a ≠ 1 → b ≠ 1 → a ≠ b →
      (∀ k ∈ K', a * k = k * a) → (∀ k ∈ K', b * k = k * b) → False)
    (hnab : ∃ k₁ ∈ K', ∃ k₂ ∈ K', k₁ * k₂ ≠ k₂ * k₁) : False := by
  classical
  have hZc := sesqNormOneScalars_le_center h B
  have hTT : T * T ∈ sesqNormOneScalars h B := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← pow_two, ← hT, pow_orderOf_eq_one]
  have hφφ : ∀ g, MulAut.conj T (MulAut.conj T g) = g := by
    intro g
    rw [MulAut.conj_apply, MulAut.conj_apply]
    have h1 := mem_center_iff.mp (hZc hTT) g
    calc T * (T * g * T⁻¹) * T⁻¹ = (T * T) * g * (T * T)⁻¹ := by group
      _ = g := by rw [← h1, mul_inv_cancel_right]
  have hφZT := map_conj_eq_of_le_center hZc T
  rw [← onQuotient_conj T hφZT] at hK
  obtain ⟨hYT, hYm, -⟩ := liftY_data (MulAut.conj T) hφZT hφφ hK
  rw [fixedSubgroup_conj] at hYT
  have hfin : finrank E V = 4 ∨ finrank E V = 5 := hdim
  obtain ⟨l, hl0, hAA, hN, hP, hM, hc, hsplit, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp (by omega) hB hBl hT
  rcases hN with hN | hN
  ·
    have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hYT.1).mp hYT
    obtain ⟨horth, hsepP, hsepM, -⟩ := hsplit hN
    obtain ⟨A, W, hAW, hA2, hset, -⟩ :=
      exists_summand_of_isComponent hp hB hBl hl0 hAA hN hP hM hY₁
    have hYset : ∀ g : sesqUnitaryGroup B, g ∈ liftY K' ↔ g ∈ summandUnitarySet B A W := by
      intro g
      rw [← hset, Subgroup.map_subgroupOf_eq_of_le hYT.1]
      rfl
    have hKset : ∀ x : sesqProjUnitary h B, x ∈ K' ↔ ∃ g ∈ summandUnitarySet B A W,
        (QuotientGroup.mk g : sesqProjUnitary h B) = x := by
      intro x
      rw [← hYm]
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact ⟨g, (hYset g).1 hg, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨g, (hYset g).2 hg, rfl⟩
    have hsymm : ∀ a w : V, B a w = h.bar (B w a) := fun a w => (hB.eq w a).symm
    rcases hAW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hdim' := Submodule.finrank_add_eq_of_isCompl hc
      exact split_false hp hB hc horth hsepP hsepM hl0
        (fun a ha => (mem_eigenPlus_iff' hl0).1 ha) (fun w hw => (mem_eigenMinus_iff' hl0).1 hw)
        hA2 (Submodule.one_le_finrank_iff.mpr hM) (by omega) hKset huniq hconj hinv2 hnab
    · have hdim' := Submodule.finrank_add_eq_of_isCompl hc
      refine split_false hp hB hc.symm (fun a ha w hw => ?_) hsepM hsepP (neg_ne_zero.mpr hl0)
        (fun a ha => ?_) (fun w hw => ?_) hA2 (Submodule.one_le_finrank_iff.mpr hP) (by omega) hKset
        huniq hconj hinv2 hnab
      · rw [hsymm, horth w hw a ha, map_zero]
      · rw [(mem_eigenMinus_iff' hl0).1 ha, neg_smul]
      · rw [(mem_eigenPlus_iff' hl0).1 hw, neg_smul, neg_neg]
  ·
    obtain ⟨-, -, -, h2m, -, -, e, hecompat, -, -⟩ := hpaired hN
    have hn4 : finrank E V = 4 := by omega
    obtain ⟨y, hy, hyz⟩ : ∃ y ∈ liftY K', QuotientGroup.mk y = (QuotientGroup.mk T : sesqProjUnitary h B) := by
      have hz : (QuotientGroup.mk T : sesqProjUnitary h B) ∈
          (liftY K').map (QuotientGroup.mk' (sesqNormOneScalars h B)) := by
        rw [hYm]; exact hmem
      obtain ⟨y, hy, hyz⟩ := hz
      exact ⟨y, hy, hyz⟩
    exact paired_false hp hn4 hl0 hN h2m e hecompat hYT hy hyz

end DLevel

end CFSG.GH74.GLS.IVK.Proofs2
