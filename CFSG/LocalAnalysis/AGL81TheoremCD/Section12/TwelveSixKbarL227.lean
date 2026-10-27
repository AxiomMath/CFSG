module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarInputs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeL2Tools
public import CFSG.GH74.GLS.IVK.L2.BorelPGL
public import CFSG.RankThree.PartTwo.KFacts.KS10L27
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.L227

open CFSG.GorensteinWalter (PSL2 PGL2 psl2FieldAut pgl2FieldAut)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (pglAction semilinearAction)
open CFSG.RankThree.PartTwo.Sec4.Item434CharThree
open CFSG.PSL2Table (mk unip)
open Matrix.ProjectiveSpecialLinearGroup (toPGL)
open CFSG.GH74.GLS.IVK.L2Borel (bor bor_conj_unip exists_eq_bor)
open CFSG.Open Subgroup

section Field

variable {F : Type} [Field F]

theorem toPGL_mk_unip_inj (h2 : (2 : F) ≠ 0) {s t : F}
    (h : toPGL (mk (unip s)) = toPGL (mk (unip t))) : s = t :=
  (CFSG.PSL2Table.mk_unip_eq_mk_unip_iff h2 s t).1
    (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h)

theorem pgl2FieldAut_unip (σ : F ≃+* F) (t : F) :
    pgl2FieldAut F σ (toPGL (mk (unip t))) = toPGL (mk (unip (σ t))) := by
  rw [← CFSG.GorensteinWalter.psl2FieldAut_toPGL]
  congr 1
  rw [CFSG.GorensteinWalter.psl2FieldAut_apply]
  change CFSG.GorensteinWalter.psl2RingEquiv σ (QuotientGroup.mk' _ (unip t)) =
    QuotientGroup.mk' _ (unip (σ t))
  rw [CFSG.GorensteinWalter.psl2RingEquiv_mk]
  congr 1
  apply CFSG.PSL2Table.SL_ext <;> simp

theorem exists_forall_conj_unip {c : PGL2 F} {s s' : F} (hs : s ≠ 0)
    (h : c * toPGL (mk (unip s)) * c⁻¹ = toPGL (mk (unip s'))) :
    ∃ l : F, ∀ t, c * toPGL (mk (unip t)) * c⁻¹ = toPGL (mk (unip (l * t))) := by
  have hb : ∀ t, bor (Units.mk0 s hs) 0 * toPGL (mk (unip t)) * (bor (Units.mk0 s hs) 0)⁻¹ =
      toPGL (mk (unip (s * t))) := fun t => by
    rw [bor_conj_unip, Units.val_mk0]
  have h1 : c * bor (Units.mk0 s hs) 0 * toPGL (mk (unip 1)) * (c * bor (Units.mk0 s hs) 0)⁻¹ =
      toPGL (mk (unip s')) := by
    calc c * bor (Units.mk0 s hs) 0 * toPGL (mk (unip 1)) * (c * bor (Units.mk0 s hs) 0)⁻¹
        = c * (bor (Units.mk0 s hs) 0 * toPGL (mk (unip 1)) * (bor (Units.mk0 s hs) 0)⁻¹) *
            c⁻¹ := by group
      _ = toPGL (mk (unip s')) := by rw [hb, mul_one, h]
  obtain ⟨a, b, hab⟩ := exists_eq_bor h1
  refine ⟨(a : F) / s, fun t => ?_⟩
  have hc : c = bor a b * (bor (Units.mk0 s hs) 0)⁻¹ := by rw [← hab, mul_inv_cancel_right]
  have h2 : (bor (Units.mk0 s hs) 0)⁻¹ * toPGL (mk (unip t)) * bor (Units.mk0 s hs) 0 =
      toPGL (mk (unip (t / s))) := by
    have e := hb (t / s)
    rw [show s * (t / s) = t by field_simp] at e
    rw [← e]
    group
  rw [hc]
  calc bor a b * (bor (Units.mk0 s hs) 0)⁻¹ * toPGL (mk (unip t)) *
        (bor a b * (bor (Units.mk0 s hs) 0)⁻¹)⁻¹
      = bor a b * ((bor (Units.mk0 s hs) 0)⁻¹ * toPGL (mk (unip t)) * bor (Units.mk0 s hs) 0) *
          (bor a b)⁻¹ := by group
    _ = toPGL (mk (unip ((a : F) / s * t))) := by
        rw [h2, bor_conj_unip, mul_div_assoc', div_mul_eq_mul_div]

theorem twisted_unip (h2 : (2 : F) ≠ 0) {g h : PGL2 F} {σ : F ≃+* F} {s s' : F} (hs : s ≠ 0)
    (h1 : g * pgl2FieldAut F σ (h * toPGL (mk (unip s)) * h⁻¹) * g⁻¹ =
      h * toPGL (mk (unip s')) * h⁻¹) :
    ∃ l : F, ∀ t t' : F, g * pgl2FieldAut F σ (h * toPGL (mk (unip t)) * h⁻¹) * g⁻¹ =
      h * toPGL (mk (unip t')) * h⁻¹ → t' = l * σ t := by
  have key : ∀ t t' : F, g * pgl2FieldAut F σ (h * toPGL (mk (unip t)) * h⁻¹) * g⁻¹ =
      h * toPGL (mk (unip t')) * h⁻¹ →
        h⁻¹ * g * pgl2FieldAut F σ h * toPGL (mk (unip (σ t))) *
          (h⁻¹ * g * pgl2FieldAut F σ h)⁻¹ = toPGL (mk (unip t')) := by
    intro t t' ht
    rw [map_mul, map_mul, map_inv, pgl2FieldAut_unip] at ht
    calc h⁻¹ * g * pgl2FieldAut F σ h * toPGL (mk (unip (σ t))) *
          (h⁻¹ * g * pgl2FieldAut F σ h)⁻¹
        = h⁻¹ * (g * (pgl2FieldAut F σ h * toPGL (mk (unip (σ t))) *
            (pgl2FieldAut F σ h)⁻¹) * g⁻¹) * h := by group
      _ = toPGL (mk (unip t')) := by rw [ht]; group
  obtain ⟨l, hl⟩ := exists_forall_conj_unip ((map_ne_zero σ).2 hs) (key s s' h1)
  exact ⟨l, fun t t' ht => (toPGL_mk_unip_inj h2 ((hl (σ t)).symm.trans (key t t' ht))).symm⟩

theorem exists_eq_pglAction_mul [Finite F] (a : MulAut (PSL2 F)) :
    ∃ (g : PGL2 F) (σ : F ≃+* F), a = pglAction F g * psl2FieldAut F σ := by
  obtain ⟨x, rfl⟩ :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_surjective F a
  refine ⟨x.left, x.right, ?_⟩
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
  rw [map_mul, CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_inl,
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_inr]

theorem conj_pglAction (g p : PGL2 F) (σ : F ≃+* F) :
    pglAction F g * psl2FieldAut F σ * pglAction F p * (pglAction F g * psl2FieldAut F σ)⁻¹ =
      pglAction F (g * pgl2FieldAut F σ p * g⁻¹) := by
  have e := DFunLike.congr_fun
    (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_fieldAut F σ) p
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply] at e
  rw [map_mul, map_mul, map_inv, e]
  group

end Field

section TwentySeven

theorem eq_zero_or_eq_one_or_eq_neg_one_of_fix {σ : GaloisField 3 3 ≃+* GaloisField 3 3}
    (hσ : σ ≠ 1) {x : GaloisField 3 3} (hx : σ x = x) : x = 0 ∨ x = 1 ∨ x = -1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hφ : frobeniusEquiv (GaloisField 3 3) 3 ∈ zpowers σ :=
    mem_zpowers_of_prime_card CFSG.RankThree.PartTwo.KFacts.card_ringAut_galoisField_three_three hσ
  have hle : zpowers σ ≤ MulAction.stabilizer (GaloisField 3 3 ≃+* GaloisField 3 3) x := by
    rw [zpowers_le, MulAction.mem_stabilizer_iff, RingAut.smul_def]
    exact hx
  have h3 : x ^ 3 = x := by
    have := hle hφ
    rwa [MulAction.mem_stabilizer_iff, RingAut.smul_def, frobeniusEquiv_def] at this
  have h0 : x * (x - 1) * (x + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.1 h0 with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (sub_eq_zero.1 h))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h))

theorem ringAut_cube (σ : GaloisField 3 3 ≃+* GaloisField 3 3) (x : GaloisField 3 3) :
    σ (σ (σ x)) = x := by
  have h := pow_card_eq_one' (x := σ)
  rw [CFSG.RankThree.PartTwo.KFacts.card_ringAut_galoisField_three_three, pow_succ, pow_two] at h
  have := congrArg (fun τ : GaloisField 3 3 ≃+* GaloisField 3 3 => τ x) h
  simp only [RingAut.mul_apply] at this
  exact this

theorem le_range_pglAction {E : Subgroup (MulAut (PSL2 (GaloisField 3 3)))}
    (hE : IsElemAbelian 3 E) (hE27 : Nat.card E = 27) :
    E ≤ (pglAction (GaloisField 3 3)).range := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (PGL2 (GaloisField 3 3)) := finite_pgl2
  obtain ⟨P, h, hPW, hP9, hPE⟩ := exists_pgl_part (by norm_num) hE hE27
  intro e he
  obtain ⟨g, σ, rfl⟩ := exists_eq_pglAction_mul e
  by_cases hσ : σ = 1
  · exact ⟨g, by rw [hσ, map_one, mul_one]⟩
  exfalso
  have hcomm : ∀ q ∈ P, g * pgl2FieldAut _ σ q * g⁻¹ = q := by
    intro q hq
    apply pglAction_injective (GaloisField 3 3)
    rw [← conj_pglAction]
    have hqE : pglAction (GaloisField 3 3) q ∈ E := hPE ⟨q, hq, rfl⟩
    have hc := congrArg Subtype.val (hE.1.is_comm.comm ⟨_, he⟩ ⟨_, hqE⟩)
    simp only [Subgroup.coe_mul] at hc
    rw [hc, mul_inv_cancel_right]
  have hPt : ∀ q ∈ P, ∃ t, q = h * toPGL (mk (unip t)) * h⁻¹ := by
    intro q hq
    obtain ⟨w, hw, rfl⟩ := hPW hq
    obtain ⟨t, rfl⟩ := exists_eq_mk_toGL_unip_of_mem hw
    exact ⟨t, rfl⟩
  obtain ⟨p₀, hp₀, hp₀1⟩ : ∃ p₀ ∈ P, p₀ ≠ 1 := by
    by_contra hno
    push Not at hno
    rw [(eq_bot_iff_forall P).2 hno, card_bot] at hP9
    omega
  obtain ⟨s, rfl⟩ := hPt p₀ hp₀
  have hs : s ≠ 0 := by
    rintro rfl
    apply hp₀1
    rw [CFSG.PSL2Table.unip_zero, map_one, map_one, mul_one, mul_inv_cancel]
  obtain ⟨l, hl⟩ := twisted_unip two_ne_zero_galois hs (hcomm _ hp₀)
  have hls := hl s s (hcomm _ hp₀)
  have hσs : σ s ≠ 0 := (map_ne_zero σ).2 hs
  have hPz : P ≤ zpowers (h * toPGL (mk (unip s)) * h⁻¹) := by
    intro q hq
    obtain ⟨t, rfl⟩ := hPt q hq
    have hlt := hl t t (hcomm _ hq)
    have hfix : σ (t / s) = t / s := by
      rw [map_div₀, div_eq_div_iff hσs hs]
      linear_combination (σ t) * hls - (σ s) * hlt
    rcases eq_zero_or_eq_one_or_eq_neg_one_of_fix hσ hfix with h0 | h1 | hm
    · rw [div_eq_zero_iff, or_iff_left hs] at h0
      rw [h0, CFSG.PSL2Table.unip_zero, map_one, map_one, mul_one, mul_inv_cancel]
      exact one_mem _
    · rw [div_eq_one_iff_eq hs] at h1
      rw [h1]
      exact mem_zpowers _
    · have ht : t = -s := by
        rw [div_eq_iff hs] at hm
        rw [hm]
        ring
      have hinv : h * toPGL (mk (unip (-s))) * h⁻¹ = (h * toPGL (mk (unip s)) * h⁻¹)⁻¹ := by
        rw [← CFSG.PSL2Table.unip_neg, map_inv, map_inv]
        group
      rw [ht, hinv]
      exact inv_mem (mem_zpowers _)
  have hcard := card_le_of_le hPz
  rw [Nat.card_zpowers] at hcard
  have h3 : orderOf (h * toPGL (mk (unip s)) * h⁻¹) ≤ 3 :=
    Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one
      (pow_three_eq_one_of_mem_map_conj (hPW hp₀)))
  omega

theorem false_of_inv_fix {E : Subgroup (MulAut (PSL2 (GaloisField 3 3)))}
    (hE : IsElemAbelian 3 E) (hE27 : Nat.card E = 27) {a v₁ v₂ : MulAut (PSL2 (GaloisField 3 3))}
    (hv₁ : v₁ ∈ E) (hv₂ : v₂ ∈ E) (h1 : v₁ ≠ 1) (h2 : v₂ ≠ 1) (ha1 : a * v₁ * a⁻¹ = v₁⁻¹)
    (ha2 : a * v₂ * a⁻¹ = v₂) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (PGL2 (GaloisField 3 3)) := finite_pgl2
  have hinj := pglAction_injective (GaloisField 3 3)
  have hEr := le_range_pglAction hE hE27
  have hP₀ : IsPGroup 3 (E.comap (pglAction (GaloisField 3 3))) := fun x => ⟨1, by
    apply Subtype.ext
    apply hinj
    rw [pow_one, Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one]
    exact hE.2 _ x.2⟩
  obtain ⟨h, hh⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := unipPGL (GaloisField 3 3))
    (by rw [card_unipPGL_galois (by norm_num), factorization_card_pgl2 (by norm_num)]) hP₀
  have hPt : ∀ q ∈ E.comap (pglAction (GaloisField 3 3)),
      ∃ t, q = h * toPGL (mk (unip t)) * h⁻¹ := by
    intro q hq
    obtain ⟨w, hw, rfl⟩ := hh hq
    obtain ⟨t, rfl⟩ := exists_eq_mk_toGL_unip_of_mem hw
    exact ⟨t, rfl⟩
  obtain ⟨p₁, rfl⟩ := hEr hv₁
  obtain ⟨p₂, rfl⟩ := hEr hv₂
  obtain ⟨t₁, rfl⟩ := hPt p₁ hv₁
  obtain ⟨t₂, rfl⟩ := hPt p₂ hv₂
  have ht : ∀ t : GaloisField 3 3,
      pglAction _ (h * toPGL (mk (unip t)) * h⁻¹) ≠ 1 → t ≠ 0 := by
    rintro t ht rfl
    apply ht
    rw [CFSG.PSL2Table.unip_zero, map_one, map_one, mul_one, mul_inv_cancel, map_one]
  have ht₁ := ht t₁ h1
  have ht₂ := ht t₂ h2
  obtain ⟨g, σ, rfl⟩ := exists_eq_pglAction_mul a
  have hinv : (h * toPGL (mk (unip t₁)) * h⁻¹)⁻¹ = h * toPGL (mk (unip (-t₁))) * h⁻¹ := by
    rw [← CFSG.PSL2Table.unip_neg, map_inv, map_inv]
    group
  have e₁ : g * pgl2FieldAut _ σ (h * toPGL (mk (unip t₁)) * h⁻¹) * g⁻¹ =
      h * toPGL (mk (unip (-t₁))) * h⁻¹ := by
    apply hinj
    rw [← conj_pglAction, ha1, ← hinv, map_inv]
  have e₂ : g * pgl2FieldAut _ σ (h * toPGL (mk (unip t₂)) * h⁻¹) * g⁻¹ =
      h * toPGL (mk (unip t₂)) * h⁻¹ := by
    apply hinj
    rw [← conj_pglAction, ha2]
  obtain ⟨l, hl⟩ := twisted_unip two_ne_zero_galois ht₂ e₂
  have hl₁ := hl t₁ (-t₁) e₁
  have hl₂ := hl t₂ t₂ e₂
  have hσx : σ (t₁ / t₂) = -(t₁ / t₂) := by
    rw [map_div₀, neg_div', div_eq_div_iff ((map_ne_zero σ).2 ht₂) ht₂]
    linear_combination (σ t₁) * hl₂ - (σ t₂) * hl₁
  have h3 := ringAut_cube σ (t₁ / t₂)
  rw [hσx, map_neg, hσx, neg_neg, hσx] at h3
  have h0 : t₁ / t₂ = 0 := by
    have h2' : (2 : GaloisField 3 3) * (t₁ / t₂) = 0 := by linear_combination -h3
    exact (mul_eq_zero.1 h2').resolve_left two_ne_zero_galois
  rw [div_eq_zero_iff] at h0
  exact h0.elim ht₁ ht₂

end TwentySeven

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.L227

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

theorem kFactL227AutE27_holds : KFactL227AutE27 := by
  intro Y _ _ hY E hE hE27 a v₁ v₂ _ hv₁ hv₂ h1 h2 ha1 ha2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, K', _, _, hK, ⟨e⟩⟩ := hY.statedClassicalModel (by decide)
  set φ := MulAut.congr
    (e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K' 2 3 3 (by norm_num) hK))
  exact L227.false_of_inv_fix (E := E.map φ.toMonoidHom) (a := φ a) (v₁ := φ v₁) (v₂ := φ v₂)
    (hE.map _) (by rw [Subgroup.card_map_of_injective φ.injective, hE27]) ⟨v₁, hv₁, rfl⟩ ⟨v₂, hv₂, rfl⟩
    (fun h => h1 (φ.injective (h.trans (map_one φ).symm)))
    (fun h => h2 (φ.injective (h.trans (map_one φ).symm)))
    (by simpa using congrArg φ ha1) (by simpa using congrArg φ ha2)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
