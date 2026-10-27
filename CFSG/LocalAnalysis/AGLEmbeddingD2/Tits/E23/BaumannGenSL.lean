module

public import CFSG.Quasithin.Background.AutSubConj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.BaumannGenAbs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.NatSL

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS5 CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS.NatSL2

section Res

variable {V : Type} [CommGroup V]

omit [CommGroup V] in
theorem eq_of_resHom_eq' {V : Type} [CommGroup V] {E : Subgroup (MulAut V)} {W : Subgroup V}
    (hEcen : E ⊓ centSub W = ⊥) {a b : stabSub W} (ha : (a : MulAut V) ∈ E)
    (hb : (b : MulAut V) ∈ E) (h : resHom W a = resHom W b) : (a : MulAut V) = b := by
  have h1 : a⁻¹ * b ∈ (resHom W).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [ker_resHom, Subgroup.mem_subgroupOf] at h1
  have h2 : (a : MulAut V)⁻¹ * b ∈ E ⊓ centSub W := ⟨E.mul_mem (E.inv_mem ha) hb, h1⟩
  rw [hEcen, Subgroup.mem_bot] at h2
  exact inv_mul_eq_one.1 h2

theorem autSub_conjSub {X : Subgroup (MulAut V)} {W : Subgroup V} {z : MulAut V}
    (hz : z ∈ stabSub W) :
    autSub (conjSub z X) W = conjSub (resHom W ⟨z, hz⟩) (autSub X W) :=
  CFSG.Quasithin.StabLat.autSub_map_conj_eq hz

end Res

section SL

variable {V : Type} [CommGroup V] [Finite V]
  {P T M : Subgroup (MulAut V)} {ℰ : Set (Subgroup (MulAut V))}
  (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1) (hF : FiveFive P T M ℰ)

include h hV hF

theorem exists_goodEl_of_slType2 {E : Subgroup (MulAut V)} (hE : E ∈ ℰ)
    (hSL : SLType2 (Hyp51.offSet P) E) {R : Subgroup (MulAut V)} (hR : R ∈ Hyp51.offSet P)
    (hRE : R ≤ E) : ∃ y, GoodEl E R y := by
  classical
  have h43 := h.hyp43 hV
  obtain ⟨n, hn, hnat, -, hsyl⟩ := id hSL
  set W := commV E with hWdef
  have hEst : E ≤ stabSub W := Subgroup.le_normalizer.trans (normalizer_commV_le_stabSub E)
  have hEcen : E ⊓ centSub W = ⊥ := IsSLNatSection.inf_centSub_eq_bot hnat
  have hL := isSLNatSection_autSub hnat hEst
  obtain ⟨D⟩ := IsSLNatSection.nonempty_natData hL (by omega)
  obtain ⟨hAN, hAE, hcardA, hquad, hidx⟩ := two_sixteen_sl hV hn hR.2.1 hR.1 (hF.le_P h hV hE)
    (hF.isSubnormal h hV hE) hnat (commutator_ne_bot_of_sl hnat hRE (h43.ne_bot R hR))
  have hAst : R ≤ stabSub W := hAN.trans (normalizer_commV_le_stabSub E)
  have hG := sylowGood_autSub hn hAst hL hAE hcardA hquad hidx
  have hRsyl : IsSylowOf 2 R E := (hsyl R).1 ⟨hR, hRE⟩
  have hRbar := isSylowOf_autSub hEst hEcen hRsyl
  obtain ⟨w₀, hw₀, hRw⟩ := D.exists_stab_of_sylow hRbar
  have hsm : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) (w : Fin 2 → GaloisField 2 n),
      g • w = (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w := fun g w => by
    rw [Matrix.SpecialLinearGroup.smul_def]; rfl
  obtain ⟨h0, hh0⟩ := exists_smul_e₁ (F := GaloisField 2 n) hw₀
  set s := sl2Three (GaloisField 2 n) with hs
  set g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) := h0 * s * h0⁻¹ with hg
  have hg3 : g ^ 3 = 1 := by
    rw [hg, conj_pow, hs, sl2Three_pow_three, mul_one, mul_inv_cancel]
  have hs1 : s ≠ 1 := sl2Three_ne_one (GaloisField 2 n)
  have hg1 : g ≠ 1 := by
    intro e
    apply hs1
    have : h0⁻¹ * g * h0 = s := by rw [hg]; group
    rw [← this, e]
    group
  have hgw : ¬ ∃ c : GaloisField 2 n, g • w₀ = c • w₀ := by
    rintro ⟨c, hc⟩
    have e1 : g • w₀ = h0 • (s • (![1, 0] : Fin 2 → GaloisField 2 n)) := by
      rw [← hh0, hg, mul_smul, mul_smul, inv_smul_smul]
    have e2 : c • w₀ = h0 • (c • (![1, 0] : Fin 2 → GaloisField 2 n)) := by
      rw [← hh0, smul_scalar_comm]
    rw [e1, e2] at hc
    have hc' : s • (![1, 0] : Fin 2 → GaloisField 2 n) = c • ![1, 0] := MulAction.injective h0 hc
    have := congrFun hc' 1
    rw [hsm] at this
    simp [hs, sl2Three, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
  have hw' : g • w₀ ≠ 0 := fun h0' => hw₀ ((smul_eq_zero_iff_eq g).1 h0')
  obtain ⟨y0, hy0E, hy0⟩ := mem_autSub.1 (D.ι_mem g)
  have hyE : (y0 : MulAut V) ∈ E := hy0E
  have hy3 : (y0 : MulAut V) ^ 3 = 1 := by
    have hres : resHom W (y0 ^ 3) = resHom W 1 := by
      rw [map_pow, hy0, ← map_pow, hg3, map_one, map_one]
    have hE3 : ((y0 ^ 3 : stabSub W) : MulAut V) ∈ E := by
      rw [Subgroup.coe_pow]; exact E.pow_mem hyE 3
    have := eq_of_resHom_eq' hEcen hE3 (b := 1) E.one_mem hres
    simpa using this
  have hy1 : (y0 : MulAut V) ≠ 1 := by
    intro e
    have : y0 = 1 := Subtype.ext e
    rw [this, map_one] at hy0
    exact hg1 (D.injective_ι (hy0.symm.trans (map_one D.ι).symm))
  have hord : orderOf (y0 : MulAut V) = 3 := orderOf_eq_prime hy3 hy1
  have hfix : ∀ w ∈ commV E, (y0 : MulAut V) w = w → w ∈ fixV E := by
    intro w hw hyw
    have h1 : D.ι g ⟨w, hw⟩ = ⟨w, hw⟩ := by
      rw [← hy0]; exact Subtype.ext hyw
    have h2 : D.vec (D.ι g ⟨w, hw⟩) = D.vec ⟨w, hw⟩ := by rw [h1]
    rw [D.vec_ι] at h2
    have h2' : g • D.vec ⟨w, hw⟩ = D.vec ⟨w, hw⟩ := h2
    have h3 : s • (h0⁻¹ • D.vec ⟨w, hw⟩) = h0⁻¹ • D.vec ⟨w, hw⟩ := by
      have := congrArg (fun v => h0⁻¹ • v) h2'
      simpa [hg, mul_smul] using this
    have h4 : h0⁻¹ • D.vec ⟨w, hw⟩ = 0 := by
      refine eq_zero_of_sl2Three_mulVec (GaloisField 2 n) ?_
      rw [← hsm]; exact h3
    have h5 : D.vec ⟨w, hw⟩ = 0 := by
      have := congrArg (fun v => h0 • v) h4
      simpa using this
    have h6 := (D.vec_eq_zero_iff _).1 h5
    intro e he
    exact mem_fixV_autSub.1 h6 e he (hEst he)
  have hR'E : conjSub (y0 : MulAut V) R ≤ E := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have := E.mul_mem (E.mul_mem hyE (hRE hx)) (E.inv_mem hyE)
    simpa [mul_assoc] using this
  have hR'st : conjSub (y0 : MulAut V) R ≤ stabSub W := hR'E.trans hEst
  have hR'w : autSub (conjSub (y0 : MulAut V) R) W = D.stab (g • w₀) := by
    rw [autSub_conjSub y0.2, hRw]
    have hy0'' : resHom W ⟨(y0 : MulAut V), y0.2⟩ = D.ι g := hy0
    rw [hy0'']
    show conjSub (D.ι g) ((stabVec w₀).map D.ι) = (stabVec (g • w₀)).map D.ι
    rw [D.conjSub_map, stabVec_smul]
  have hsup := D.stab_sup_eq hw₀ hw' hgw
  have hgen : E ≤ R ⊔ conjSub (y0 : MulAut V) R := by
    intro e he
    have h1 : resHom W ⟨e, hEst he⟩ ∈ autSub E W := mem_autSub.2 ⟨⟨e, hEst he⟩, he, rfl⟩
    rw [← hsup, ← hRw, ← hR'w] at h1
    have h2 : resHom W ⟨e, hEst he⟩ ∈ autSub (R ⊔ conjSub (y0 : MulAut V) R) W :=
      (sup_le (autSub_mono le_sup_left W) (autSub_mono le_sup_right W)) h1
    obtain ⟨a, haR, hae⟩ := mem_autSub.1 h2
    have h3 : (a : MulAut V) = e :=
      eq_of_resHom_eq' hEcen (a := a) (b := ⟨e, hEst he⟩) (sup_le hRE hR'E haR) he hae
    rw [← h3]
    exact haR
  have hfs := D.fixV_stab_inf_sup hG hw₀ hw' hgw
  have hsplit : ∀ w ∈ commV E, ∃ a ∈ commV E ⊓ fixV R,
      ∃ b ∈ commV E ⊓ fixV (conjSub (y0 : MulAut V) R), w = a * b := by
    intro w hw
    have hu : (⟨w, hw⟩ : ↥W) ∈ fixV (D.stab w₀) ⊔ fixV (D.stab (g • w₀)) := by
      rw [hfs.2]; exact Subgroup.mem_top _
    obtain ⟨a', ha', b', hb', hab⟩ := Subgroup.mem_sup.1 hu
    rw [← hRw] at ha'
    rw [← hR'w] at hb'
    exact ⟨a', ⟨a'.2, fun r hr => mem_fixV_autSub.1 ha' r hr (hAst hr)⟩, b',
      ⟨b'.2, fun r hr => mem_fixV_autSub.1 hb' r hr (hR'st hr)⟩, (congrArg Subtype.val hab).symm⟩
  exact ⟨(y0 : MulAut V), ⟨hyE, hord, hgen, hfix, hsplit⟩⟩

end SL

end CFSG.AGLEmbeddingD2.Tits.E23
