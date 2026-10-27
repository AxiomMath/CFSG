module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnAPI
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4OutQuot

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] noncomputable def conjQuot (Q : Type) [Group Q] : Q ⧸ Subgroup.center Q →* MulAut Q :=
  QuotientGroup.lift (Subgroup.center Q) MulAut.conj (by
    intro z hz
    rw [MonoidHom.mem_ker]
    ext x
    have h := Subgroup.mem_center_iff.1 hz x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h, mul_inv_cancel_right])

theorem conjQuot_mk {Q : Type} [Group Q] (g : Q) :
    conjQuot Q (QuotientGroup.mk g) = MulAut.conj g := rfl

theorem conj_eq_conj_iff {Q : Type} [Group Q] (a b : Q) :
    MulAut.conj a = MulAut.conj b ↔ a⁻¹ * b ∈ Subgroup.center Q := by
  constructor
  · intro h
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := congrArg (fun φ : MulAut Q => φ (a * x * a⁻¹)) h
    simp only [MulAut.conj_apply] at hx
    have h2 : ∀ y : Q, b * y * b⁻¹ = a * y * a⁻¹ := fun y => by
      have := congrArg (fun φ : MulAut Q => φ y) h
      simpa [MulAut.conj_apply] using this.symm
    have h3 := h2 x
    calc x * (a⁻¹ * b) = a⁻¹ * (a * x * a⁻¹) * b := by group
      _ = a⁻¹ * (b * x * b⁻¹) * b := by rw [h2 x]
      _ = a⁻¹ * b * x := by group
  · intro h
    ext x
    simp only [MulAut.conj_apply]
    have h1 := Subgroup.mem_center_iff.1 h
    symm
    calc b * x * b⁻¹ = a * ((a⁻¹ * b) * x * (a⁻¹ * b)⁻¹) * a⁻¹ := by group
      _ = a * x * a⁻¹ := by rw [← h1 x, mul_inv_cancel_right]

theorem conjQuot_injective (Q : Type) [Group Q] : Function.Injective (conjQuot Q) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
  rw [conjQuot_mk] at hs
  rw [QuotientGroup.eq_one_iff]
  have h1 : MulAut.conj g = MulAut.conj (1 : Q) := by rw [hs, map_one]
  simpa using (conj_eq_conj_iff g 1).1 h1

theorem range_conjQuot (Q : Type) [Group Q] : (conjQuot Q).range = innerAut Q := by
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨QuotientGroup.mk g, rfl⟩

theorem map_u4Fix_conjQuot {Q : Type} [Group Q] (v : MulAut Q) :
    (u4Fix (u4AutQuot Q v)).map (conjQuot Q) =
      innerAut Q ⊓ Subgroup.centralizer ({v} : Set (MulAut Q)) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
    have hs' : u4AutQuot Q v (QuotientGroup.mk g) = QuotientGroup.mk g := hs
    rw [u4AutQuot_mk] at hs'
    have hc : MulAut.conj (v g) = MulAut.conj g := by
      rw [conj_eq_conj_iff]
      have := (QuotientGroup.eq (a := v g) (b := g)).1 hs'
      exact this
    refine ⟨by rw [← range_conjQuot]; exact ⟨_, rfl⟩, ?_⟩
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    have hcj := mulAut_mul_conj_mul_inv v g
    rw [conjQuot_mk, hc] at *
    calc v * MulAut.conj g = (v * MulAut.conj g * v⁻¹) * v := by group
      _ = MulAut.conj g * v := by rw [hcj]
  · rintro ⟨hin, hcomm⟩
    rw [← range_conjQuot] at hin
    obtain ⟨s, rfl⟩ := hin
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
    refine ⟨QuotientGroup.mk g, ?_, rfl⟩
    have h1 := hcomm v (Set.mem_singleton v)
    rw [conjQuot_mk] at h1
    have hcj := mulAut_mul_conj_mul_inv v g
    have hc : MulAut.conj (v g) = MulAut.conj g := by
      rw [← hcj]
      calc v * MulAut.conj g * v⁻¹ = (MulAut.conj g * v) * v⁻¹ := by rw [h1]
        _ = MulAut.conj g := by group
    show u4AutQuot Q v (QuotientGroup.mk g) = QuotientGroup.mk g
    rw [u4AutQuot_mk]
    exact (QuotientGroup.eq).2 ((conj_eq_conj_iff _ _).1 hc)

@[expose] noncomputable def equivFix {Q : Type} [Group Q] (v : MulAut Q) :
    ↥(u4Fix (u4AutQuot Q v)) ≃*
      ↥(innerAut Q ⊓ Subgroup.centralizer ({v} : Set (MulAut Q))) :=
  (Subgroup.equivMapOfInjective _ (conjQuot Q) (conjQuot_injective Q)).trans
    (MulEquiv.subgroupCongr (map_u4Fix_conjQuot v))

theorem glaPrimeCoreOf_inf_centralizer_eq_bot {Q : Type} [Group Q] (v : MulAut Q)
    (h : GLAPPrimeCore 3 ↥(u4Fix (u4AutQuot Q v)) = ⊥) :
    GLAPPrimeCoreOf 3 (innerAut Q ⊓ Subgroup.centralizer ({v} : Set (MulAut Q))) = ⊥ := by
  have h1 : GLAPPrimeCore 3 ↥(innerAut Q ⊓ Subgroup.centralizer ({v} : Set (MulAut Q))) = ⊥ := by
    have := CFSG.pPrimeCore_map_iso 3 (equivFix v)
    have h' : CFSG.pPrimeCore 3 ↥(u4Fix (u4AutQuot Q v)) = ⊥ := h
    show CFSG.pPrimeCore 3 ↥(innerAut Q ⊓ Subgroup.centralizer ({v} : Set (MulAut Q))) = ⊥
    rw [← this, h', Subgroup.map_bot]
  show (GLAPPrimeCore 3 ↥(innerAut Q ⊓ Subgroup.centralizer ({v} : Set (MulAut Q)))).map
    (innerAut Q ⊓ Subgroup.centralizer ({v} : Set (MulAut Q))).subtype = ⊥
  rw [h1, Subgroup.map_bot]

theorem hasU4Quot_of_u4Hyp {Q : Type} [Group Q] [Finite Q] (v : MulAut Q) (hU : U4Hyp v) :
    HasU4Quot (u4Fix (u4AutQuot Q v)) := by
  obtain ⟨J, hJsub, hJq, hJcat⟩ := hU
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hPn : Nat.card (PSimple 3 J) = 25920 := card_of_catalogIs_u4two hJcat
  haveI : IsSimpleGroup (PSimple 3 J) := hJq.2
  let Φ : ↥J →* (Q ⧸ Subgroup.center Q) :=
    (QuotientGroup.mk' (Subgroup.center Q)).comp J.subtype
  let Ψ : ↥J →* PSimple 3 J :=
    (QuotientGroup.mk' (Subgroup.center (PQuot 3 J))).comp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J))
  have hΨ : Function.Surjective Ψ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hker : Φ.ker ≤ Ψ.ker := by
    intro j hj
    rw [MonoidHom.mem_ker] at hj ⊢
    have hjc : (j : Q) ∈ Subgroup.center Q := (QuotientGroup.eq_one_iff (j : Q)).1 hj
    have hx : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) j : PQuot 3 J) ∈
        Subgroup.center (PQuot 3 J) := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective r
      simp only [QuotientGroup.mk'_apply]
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_center_iff.1 hjc (k : Q)
    exact (QuotientGroup.eq_one_iff _).2 hx
  have hA : Φ.range ≤ u4Fix (u4AutQuot Q v) := by
    rintro _ ⟨j, rfl⟩
    show u4AutQuot Q v (QuotientGroup.mk (j : Q)) = QuotientGroup.mk (j : Q)
    rw [u4AutQuot_mk]
    have : v (j : Q) = (j : Q) := hJsub.le j.2
    rw [this]
  let f : ↥Φ.range →* PSimple 3 J :=
    (QuotientGroup.lift Φ.ker Ψ hker).comp (QuotientGroup.quotientKerEquivRange Φ).symm.toMonoidHom
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨j, rfl⟩ := hΨ y
    refine ⟨(QuotientGroup.quotientKerEquivRange Φ) (QuotientGroup.mk j), ?_⟩
    simp [f]
  exact HasU4Quot.of_surj hA hPn f hf

@[expose] def U4InnAt (P : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], catalogIs S P → U4InnModel S

theorem U4InnAt.mono {P P' : TauCeti.CFSGIndex → Prop} (hPP : ∀ i, P i → P' i)
    (h : U4InnAt P') : U4InnAt P := fun S _ _ hc =>
  h S (by obtain ⟨i, hi, e⟩ := hc; exact ⟨i, hPP i hi, e⟩)

theorem U4InnAt.of_or {P₁ P₂ : TauCeti.CFSGIndex → Prop} (h₁ : U4InnAt P₁) (h₂ : U4InnAt P₂) :
    U4InnAt (fun i => P₁ i ∨ P₂ i) := fun S _ _ hc => by
  obtain ⟨i, hi | hi, e⟩ := hc
  · exact h₁ S ⟨i, hi, e⟩
  · exact h₂ S ⟨i, hi, e⟩

theorem u4AutQuot_pow_three {Q : Type} [Group Q] {v : MulAut Q} (hv : v ^ 3 = 1) :
    u4AutQuot Q v ^ 3 = 1 := by
  have h : u4AutQuotHom Q (v ^ 3) = 1 := by rw [hv, map_one]
  rwa [map_pow] at h

theorem u4InnRest_of_main (h : U4InnAt (fun i => S9.isTableU4 i ∧ ¬ S9.isU4two i)) : U4InnRest := by
  intro Q _ _ v hQ _hO hcat hv3 hU
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  exact glaPrimeCoreOf_inf_centralizer_eq_bot v
    (h _ hcat inferInstance (u4AutQuot Q v) (u4AutQuot_pow_three hv3) (hasU4Quot_of_u4Hyp v hU))

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
