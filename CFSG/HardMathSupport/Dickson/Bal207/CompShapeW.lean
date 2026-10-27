module

public import CFSG.HardMathSupport.Dickson.Bal207.CompShape
public import CFSG.HardMathSupport.Dickson.Bal207.GlueNorm

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux CFSG.HardMathSupport.Dickson.I271

open scoped commutatorElement

structure CompShapeW (p : ℕ) (T : ∀ (Q : Type) [Group Q], Prop) {S : Type} [Group S]
    (β : MulAut S) : Prop where
  layer : PerfectInLayer β
  type : ∀ L : Subgroup S, IsComponentOf L (fixSubgroup β) → T (↥L ⧸ Subgroup.center ↥L)
  norm : ∀ ω : MulAut S, ω * β = β * ω → ω ^ p = 1 → ∀ L : Subgroup S,
    IsComponentOf L (fixSubgroup β) → L.map ω.toMonoidHom = L
  moved : ∀ ω : MulAut S, ω * β = β * ω → ∀ L : Subgroup S, IsComponentOf L (fixSubgroup β) →
    L.map ω.toMonoidHom ≠ L → Subgroup.center ↥L = ⊥

theorem CompShape.compShapeW {T : ∀ (Q : Type) [Group Q], Prop} {S : Type} [Group S]
    {β : MulAut S} (h : CompShape T β) (p : ℕ) : CompShapeW p T β :=
  ⟨h.layer, h.type, fun ω hω _ L hL => h.norm ω hω L hL,
    fun ω hω L hL hne => absurd (h.norm ω hω L hL) hne⟩

section Congr

variable {S G : Type} [Group S] [Group G]

private theorem map_map_congr (e : S ≃* G) (ω : MulAut S) (L : Subgroup S) :
    (L.map (e : S →* G)).map (MulAut.congr e ω).toMonoidHom =
      (L.map ω.toMonoidHom).map (e : S →* G) := by
  have hc : ((MulAut.congr e ω).toMonoidHom.comp (e : S →* G)) =
      (e : S →* G).comp ω.toMonoidHom := by
    ext x
    show e (ω (e.symm (e x))) = e (ω x)
    rw [MulEquiv.symm_apply_apply]
  rw [Subgroup.map_map, hc, ← Subgroup.map_map]

end Congr

section Rigid

variable {S : Type} [Group S]

private theorem isComponentOf_map_of_commute_w {β ω : MulAut S} (h : ω * β = β * ω) {L : Subgroup S}
    (hL : IsComponentOf L (fixSubgroup β)) :
    IsComponentOf (L.map ω.toMonoidHom) (fixSubgroup β) := by
  have hc : MulAut.congr ω β = β := by
    ext y
    rw [MulAut.congr_apply]
    have := congrArg (fun φ : MulAut S => φ (ω.symm y)) h
    simp only [MulAut.mul_apply, MulEquiv.apply_symm_apply] at this
    exact this
  have h2 : (fixSubgroup β).map (ω : S →* S) = fixSubgroup β := by
    have h3 := fixSubgroup_mulAutCongr ω β
    rw [hc] at h3
    exact h3.symm
  have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map ω hL
  rw [h2] at h1
  exact h1

end Rigid

private theorem dvd_card_of_glaPComponent {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {Y J : Subgroup G} (hJ : GLAPComponent p Y J) : p ∣ Nat.card J := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hQ : CFSG.Open.IsQuasisimple (↥J ⧸ GLAPPrimeCore p ↥J) := by
    have h1 := glaPComponent_of_le hp hJ le_rfl hJ.1
    have h2 := h1.2.2.1.2.2
    change CFSG.Open.IsQuasisimple ↥(barX p J J) at h2
    rw [barX_self] at h2
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv Subgroup.topEquiv h2
  set P : Subgroup ↥J := GLAPPrimeCore p ↥J with hPdef
  have hQnt : Nontrivial (↥J ⧸ P) := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    have := hQ.2.toNontrivial
    have : Subsingleton ((↥J ⧸ P) ⧸ Subgroup.center (↥J ⧸ P)) :=
      (QuotientGroup.mk'_surjective (Subgroup.center (↥J ⧸ P))).subsingleton
    exact not_subsingleton _ this
  have hdvd : p ∣ Nat.card (↥J ⧸ P) := by
    by_contra hnd
    have hc : Nat.Coprime p (Nat.card (↥J ⧸ P)) := (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
    have hbot : GLAPPrimeCore p (↥J ⧸ P) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p
    have htop : (⊤ : Subgroup (↥J ⧸ P)) ≤ GLAPPrimeCore p (↥J ⧸ P) :=
      le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩
    rw [hbot] at htop
    obtain ⟨u, v, huv⟩ := exists_pair_ne (↥J ⧸ P)
    exact huv ((Subgroup.mem_bot.1 (htop (Subgroup.mem_top u))).trans
      (Subgroup.mem_bot.1 (htop (Subgroup.mem_top v))).symm)
  have h2 : Nat.card (↥J ⧸ P) ∣ Nat.card J := by
    have := Subgroup.index_dvd_card P
    simpa [Subgroup.index] using this
  exact hdvd.trans h2

section Clauses

variable {X : Type} [Group X]

theorem mem_normalizer_of_exists_comm_moved [Finite X] {p : ℕ} (hp : p.Prime)
    {K B : Subgroup X} {a w : X} (hBK : B ≤ Subgroup.normalizer (K : Set X))
    (hw : w ∈ Subgroup.normalizer (K : Set X))
    (hwa : w * a * w⁻¹ * a⁻¹ ∈ Subgroup.centralizer (K : Set X))
    (hwB : ∀ b ∈ B, ⁅w, b⁆ ∈ Subgroup.centralizer (K : Set X))
    {J : Subgroup X} (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J)
    (hmove : GLBConj w J ≠ J →
      ∃ b ∈ B, b ∈ GLBConj w J ∧ ∃ y ∈ GLBConj w J, ⁅b, y⁆ ∉ GLAPPrimeCoreOf p (GLBConj w J)) :
    w ∈ Subgroup.normalizer (J : Set X) := by
  have hJ'c : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) (GLBConj w J) :=
    Glue.glaPComponent_gLBConj_of_comm hw hwa hJ
  by_cases hJJ : GLBConj w J = J
  · exact mem_normalizer_iff_gLBConj_eq.2 hJJ
  · exfalso
    obtain ⟨b, hbB, hbJ', y, hyJ', hy⟩ := hmove hJJ
    have hbw : w * b * w⁻¹ ∈ J := mem_gLBConj.1 hbJ'
    have hcomm := commutator_mem_gLAPPrimeCoreOf_of_ne hp hJ'c hJ hJJ hbw hyJ'
    set z : X := ⁅w, b⁆ with hz
    have hzC : z ∈ Subgroup.centralizer (K : Set X) := hwB b hbB
    have hyK : y ∈ K := (hJ'c.1 hyJ').1
    have hbyK : b * y * b⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hBK hbB) y).1 hyK
    have hzby : z * (b * y * b⁻¹) = (b * y * b⁻¹) * z :=
      (Subgroup.mem_centralizer_iff.1 hzC _ hbyK).symm
    have hc : w * b * w⁻¹ = z * b := by
      rw [hz, commutatorElement_def]
      group
    have e : (w * b * w⁻¹) * y * (w * b * w⁻¹)⁻¹ * y⁻¹ = ⁅b, y⁆ := by
      rw [hc, commutatorElement_def]
      calc z * b * y * (z * b)⁻¹ * y⁻¹ = (z * (b * y * b⁻¹) * z⁻¹) * y⁻¹ := by group
        _ = ((b * y * b⁻¹) * z * z⁻¹) * y⁻¹ := by rw [hzby]
        _ = b * y * b⁻¹ * y⁻¹ := by group
    rw [e] at hcomm
    exact hy hcomm

end Clauses

end CFSG.HardMathSupport.Dickson.Bal207
