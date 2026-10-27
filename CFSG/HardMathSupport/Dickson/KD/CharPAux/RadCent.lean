module

public import CFSG.HardMathSupport.Dickson.KD.CharPAux.Layer
public import CFSG.GH74.GLS.Stage2.OddAut.RPData

public section

namespace CFSG.HardMathSupport.Dickson.KD

open CFSG.Open CFSG.LieType.BorelTits CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem radCent_of_pCharData {C : Type} [Group C] [Finite C] {p : ℕ} [Fact p.Prime]
    {A : Subgroup (MulAut C)} (hInnA : (MulAut.conj : C →* MulAut C).range ≤ A)
    (hcen : Subgroup.center C = ⊥) (hd : PCharData C p A) : RadCent C p := by
  intro R hRne hRp hcore hNne hSyl
  obtain ⟨S, hS⟩ := hSyl
  obtain ⟨Q, hQP, hQn, hQp, hQr⟩ := hd S (Subgroup.normalizer (R : Set C)) hS hNne
  have hQR : Q ≤ R := by
    rw [← hcore]
    exact le_pCoreOf p hQP hQn hQp
  have hinj := mulAut_conj_injective_of_center_bot hcen
  intro c hc
  have hcQ : ∀ q ∈ Q, (MulAut.conj c : MulAut C) q = q := by
    intro q hq
    have h1 : q * c = c * q := Subgroup.mem_centralizer_iff.1 hc q (hQR hq)
    simp only [MulAut.conj_apply]
    rw [← h1]
    group
  obtain ⟨q, hq, hqc⟩ := hQr (MulAut.conj c) (hInnA ⟨c, rfl⟩) hcQ
  have : q = c := hinj hqc
  exact this ▸ hQR hq

theorem RadCent.of_mulEquiv {S T : Type*} [Group S] [Group T] [Finite S] {p : ℕ} [Fact p.Prime]
    (e : S ≃* T)
    (h : RadCent T p) : RadCent S p := by
  intro R hRne hRp hcore hNne hSyl
  obtain ⟨Sy, hSy⟩ := hSyl
  set R' : Subgroup T := R.map e.toMonoidHom with hR'
  have hnorm : (Subgroup.normalizer (R : Set S)).map e.toMonoidHom =
      Subgroup.normalizer (R' : Set T) := Subgroup.map_equiv_normalizer_eq R e
  have hR'ne : R' ≠ ⊥ := by
    intro hb
    apply hRne
    rwa [hR', Subgroup.map_eq_bot_iff_of_injective _ e.injective] at hb
  have hcore' : pCoreOf p (Subgroup.normalizer (R' : Set T)) = R' := by
    rw [← hnorm, pCoreOf_map_mulEquiv, hcore]
  have hNne' : Subgroup.normalizer (R' : Set T) ≠ ⊤ := by
    rw [← hnorm]
    intro htop
    apply hNne
    have := congrArg (Subgroup.map e.symm.toMonoidHom) htop
    rw [Subgroup.map_map] at this
    have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id S := by ext x; simp
    rw [hid, Subgroup.map_id] at this
    rw [this]
    exact Subgroup.map_top_of_surjective _ e.symm.surjective
  have hSyl' : ∃ Sy' : Sylow p T, Subgroup.normalizer ((Sy' : Subgroup T) : Set T) ≤
      Subgroup.normalizer (R' : Set T) := by
    have hsurj : Function.Surjective e.toMonoidHom := e.surjective
    refine ⟨Sylow.mapSurjective hsurj Sy, ?_⟩
    rw [Sylow.coe_mapSurjective, ← Subgroup.map_equiv_normalizer_eq, ← hnorm]
    exact Subgroup.map_mono hSy
  have hC := h R' hR'ne (hRp.map _) hcore' hNne' hSyl'
  intro c hc
  have hec : e c ∈ Subgroup.centralizer (R' : Set T) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨r, hr, rfl⟩
    show e r * e c = e c * e r
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hc r hr]
  obtain ⟨r, hr, hrc⟩ := hC hec
  have : r = c := e.injective hrc
  exact this ▸ hr

@[expose] def KDCharPAt (p : ℕ) (S : Type*) [Group S] : Prop :=
  ∀ u : S, orderOf u = p → GLAPLayer p (Subgroup.centralizer ({u} : Set S)) = ⊥

theorem kdCharPAt_of_model {S Y : Type} [Group S] [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    (e : S ≃* Y) (hBT : Holds Y p) (hcen : Subgroup.center Y = ⊥) (hd : PCharData Y p ⊤) :
    KDCharPAt p S := by
  haveI : Finite S := Finite.of_equiv Y e.symm.toEquiv
  intro u hu
  exact gLAPLayer_centralizer_eq_bot_of_holds (hBT.of_mulEquiv e.symm)
    (RadCent.of_mulEquiv e (radCent_of_pCharData le_top hcen hd)) hu

end CFSG.HardMathSupport.Dickson.KD
