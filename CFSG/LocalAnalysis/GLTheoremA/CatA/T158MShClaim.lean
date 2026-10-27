module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShSetupDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.CtxHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShNotD4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cClause
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevAutFieldGraph
public import CFSG.GroupTheory.PLayer.Bootstrap
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158Fg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GSplit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MInn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Uni
public import CFSG.GroupTheory.SupCommute
import CFSG.Adapters.Certificate43Check
public import TauCeti.GroupTheory.ExponentPrime

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.K155X
open CFSG.LocalAnalysis.GLTheoremA.T171Sh
open scoped commutatorElement

@[expose] def T158MISetup : Prop :=
  (∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L A : Subgroup G),
    A ≤ Subgroup.normalizer (L : Set G) →
    (∀ a ∈ A, InnDiagOn p (Subgroup.zpowers a) L) → InnDiagOn p A L) ∧
  (∀ (G : Type) [Group G] [Finite G] (p : ℕ) (X L : Subgroup G) (g : G),
    GLAPComponent p X L → FieldOn p g L → ¬ InnDiagOn p (Subgroup.zpowers g) L)

theorem PreSetup.not_innDiagOn_of_mi (hMI : T158MISetup) {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} (hpre : PreSetup p L J A d b) :
    ¬ InnDiagOn p (Subgroup.zpowers b) J := by
  rcases hpre.fg with hF | hG
  · exact hMI.2 G p (L ⊓ Subgroup.centralizer ({d} : Set G)) J b hpre.pcomp hF
  · exact hG.1.2

theorem t158SetupLU_of_mi (hMI : T158MISetup) (hC : T158CompLU) (hCl : T158ClaimLU) :
    T158SetupLU := by
  intro G _ _ p L J A d b N hpre hcat
  have hC' := hC G p L J A d b N hpre hcat
  have hcomp := hC'.1
  have h2p := hC'.2.1
  have hcatJ := hC'.2.2
  have hElem : ∀ a ∈ A, InnDiagOn p (Subgroup.zpowers a) L :=
    hCl G p L J A d b N hpre hcat hcomp.2 hcatJ
  have hInnA : InnDiagOn p A L := hMI.1 G p L A hpre.norm hElem
  have hidiag : InnerDiagMarking A L :=
    (S10.innDiagOn_iff (glaPComponent_self_p hpre.qs hpre.core) hpre.qs).2 hInnA
  have hnonID : ¬ InnDiagOn p (Subgroup.zpowers b) J := hpre.not_innDiagOn_of_mi hMI
  refine ⟨Setup.mk hpre.prime hpre.odd hpre.qs hpre.chev2 hpre.elem hidiag hpre.faithful
    hpre.d_mem hpre.d_ne hpre.b_mem hcomp hpre.pcomp hpre.chevJ hpre.b_norm hnonID, h2p⟩

section CertsSetup

theorem t158MISetup_holds : T158MISetup := by
  haveI := CFSG.Adapters.certificate43_holds
  exact ⟨fun _ _ _ _ _ _ hA h => MI.innDiag_unif_holds (L := _) (A := _) hA h,
    fun _ _ _ _ _ _ _ hL hF => (MI.field_nonInnDiag_any hL hF).2⟩

theorem t158SetupLU_of (hC : T158CompLU) (hCl : T158ClaimLU) : T158SetupLU :=
  t158SetupLU_of_mi t158MISetup_holds hC hCl

end CertsSetup

section CertsClaim

private theorem shape_catalog_of_I171 {p N : ℕ} {S : Type} [Group S]
    (h : catalogIs S (onLie fun i => ∃ q,
      (i = .A (N - 1) q ∨ i = .twistedA (N - 1) q) ∧ I171.I171LieShape p i)) :
    catalogIs S (onLie fun i => ∃ n q, q.p = 2 ∧ (i = .A n q ∨ i = .twistedA n q)) := by
  refine catalogIs_imp (fun i hi => ?_) h
  cases i with
  | lie d =>
    obtain ⟨q, hq, hshape⟩ := hi
    rcases hq with hq | hq <;> rw [hq] at hshape
    · exact ⟨N - 1, q, hshape.1, Or.inl hq⟩
    · exact ⟨N - 1, q, hshape.1, Or.inr hq⟩
  | cyclic _ _ => simp [onLie] at hi
  | alternating _ _ => simp [onLie] at hi
  | sporadic _ => simp [onLie] at hi

private theorem shape_lin_or_uni {p N : ℕ} {S : Type} [Group S]
    (h : catalogIs S (onLie fun i => ∃ q,
      (i = .A (N - 1) q ∨ i = .twistedA (N - 1) q) ∧ I171.I171LieShape p i)) :
    catalogIs S l154Lin ∨ catalogIs S l154Uni := by
  obtain ⟨d, hv, hd, ⟨e⟩⟩ := K144I.exists_lieIndex_of_catalogIs_onLie h
  obtain ⟨q, hq, hshape⟩ := hd
  rcases hq with rfl | rfl
  · exact Or.inl ⟨TauCeti.CFSGIndex.lie ⟨.A (N - 1) q, hv⟩, hshape.1, ⟨e⟩⟩
  · exact Or.inr ⟨TauCeti.CFSGIndex.lie ⟨.twistedA (N - 1) q, hv⟩, hshape.1, ⟨e⟩⟩

private theorem fieldOn_of_notInnDiag_of_shape {G : Type} [Group G] [Finite G] {p N : ℕ}
    (hc : CatDistinct.Ctx) (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G} {a : G}
    (hL : GLAPComponent p L L) (hchev : IsChevSimple 2 (PSimple p L))
    (hcat : catalogIs (PSimple p L) (onLie fun i => ∃ q,
      (i = .A (N - 1) q ∨ i = .twistedA (N - 1) q) ∧ I171.I171LieShape p i))
    (haN : a ∈ Subgroup.normalizer (L : Set G)) (hap : a ^ p = 1)
    (hnon : ¬ InnDiagOn p (Subgroup.zpowers a) L) :
    FieldOn p a L := by
  haveI := CFSG.Adapters.certificate43_holds
  rcases (i91_holds G p) hp hp2 L L a hL hchev haN hap ⟨haN, hnon⟩ with hF | ⟨hp3, hD | hT⟩
  · exact hF
  · subst hp3
    exact absurd hD ((not_d4_of_linUni_two hc (shape_catalog_of_I171 hcat)).1)
  · subst hp3
    exact absurd hT ((not_d4_of_linUni_two hc (shape_catalog_of_I171 hcat)).2)

private theorem shape_catalog_of_J {p N : ℕ} {S : Type} [Group S]
    (h : catalogIs S (onLie fun i => ∃ q, q.p = 2 ∧
      (i = .A (N / p - 1) q ∨ i = .twistedA (N / p - 1) q))) :
    catalogIs S (onLie fun i => ∃ n q, q.p = 2 ∧ (i = .A n q ∨ i = .twistedA n q)) := by
  refine catalogIs_imp (Q := onLie fun i => ∃ q, q.p = 2 ∧
    (i = .A (N / p - 1) q ∨ i = .twistedA (N / p - 1) q))
    (Q' := onLie fun i => ∃ n q, q.p = 2 ∧ (i = .A n q ∨ i = .twistedA n q)) ?_ h
  intro i hi
  cases i with
  | lie d => exact ⟨N / p - 1, hi⟩
  | cyclic _ _ => simp [onLie] at hi
  | alternating _ _ => simp [onLie] at hi
  | sporadic _ => simp [onLie] at hi

theorem t158ClaimLU_of (hc : CatDistinct.Ctx) : T158ClaimLU := by
  haveI := CFSG.Adapters.certificate43_holds
  intro G _ _ p L J A d b N hpre hcatL hJlayer hcatJ a ha
  by_contra hnot
  haveI : Fact p.Prime := ⟨hpre.prime⟩
  have hp := hpre.prime
  have hp2 := hpre.odd
  have hLself : GLAPComponent p L L := glaPComponent_self_p hpre.qs hpre.core
  have hdA : d ∈ A := hpre.d_mem
  have hbA : b ∈ A := hpre.b_mem
  have hdbInn : InnDiagOn p (Subgroup.zpowers d ⊔ Subgroup.zpowers b) L :=
    (S10.innDiagOn_iff hLself hpre.qs).1 hpre.idiag₂
  have hbInn : InnDiagOn p (Subgroup.zpowers b) L :=
    S10.innDiagOn_mono hdbInn (le_sup_right)
  have hdInn : InnDiagOn p (Subgroup.zpowers d) L :=
    S10.innDiagOn_mono hdbInn (le_sup_left)
  have haN_L : a ∈ Subgroup.normalizer (L : Set G) := hpre.norm ha
  have hap : a ^ p = 1 := hpre.elem.2 a ha
  have hqJ : CFSG.Open.IsQuasisimple (PQuot p J) :=
    isQuasisimple_pQuot_of_glaPComponent hp hpre.pcomp
  have hbotL : InnDiagOn p (⊥ : Subgroup G) L := S10.innDiagOn_mono hdbInn bot_le
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hnot (by simpa using hbotL)
  have horda : orderOf a = p := orderOf_eq_prime hap ha1
  have hnotab : a ∉ Subgroup.zpowers b := fun h =>
    hnot (S10.innDiagOn_mono hbInn (Subgroup.zpowers_le.2 h))
  have hab : a * b = b * a := isElemAbelian_commute hpre.elem ha hbA
  have haN_J : a ∈ Subgroup.normalizer (J : Set G) := by
    have hX := CFSG.LocalAnalysis.GLTheoremA.H1431c.normalizer_inf_centralizer haN_L
      (isElemAbelian_commute hpre.elem ha hdA)
    simpa [hJlayer] using CFSG.LocalAnalysis.GLTheoremA.S12.mem_normalizer_glaLayer' hX
  have hfield_a : FieldOn p a L :=
    fieldOn_of_notInnDiag_of_shape hc hp hp2 hLself hpre.chev2 hcatL haN_L hap hnot
  have hshapeQ : catalogIs (PSimple p L) l154Lin ∨ catalogIs (PSimple p L) l154Uni :=
    shape_lin_or_uni hcatL
  let H : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers b
  have hHA : H ≤ A := sup_le (Subgroup.zpowers_le.2 ha) (Subgroup.zpowers_le.2 hbA)
  have hHnorm : H ≤ Subgroup.normalizer (J : Set G) :=
    sup_le (Subgroup.zpowers_le.2 haN_J) (Subgroup.zpowers_le.2 hpre.b_norm)
  have hHexp : ∀ c ∈ H, c ^ p = 1 := fun c hc => hpre.elem.2 c (hHA hc)
  have hcommH : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, Commute x y := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact Commute.zpow_zpow (show Commute a b from hab) i j
  have hbInnJ0 : ¬ InnDiagOn p (Subgroup.zpowers b) J :=
    hpre.not_innDiagOn_of_mi t158MISetup_holds
  have hb1 : b ≠ 1 := by
    intro h1
    have hbN1 : (⟨b, hpre.b_norm⟩ : Subgroup.normalizer (J : Set G)) = 1 := Subtype.ext h1
    have h1chev : chevAut p J ⟨b, hpre.b_norm⟩ = 1 := by
      rw [hbN1]
      exact map_one _
    exact chevAut_ne_one_of_fgOn hp hpre.odd hpre.b_norm
      (even_card_pSimple hp hpre.pcomp) hpre.fg h1chev
  have hHcard_b : Nat.card (Subgroup.zpowers b) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hpre.elem.2 b hbA) hb1]
  have hHcard : Nat.card H = p ^ 2 := by
    have h := CFSG.card_zpowers_sup_zpowers_eq_prime_sq hp
      (hpre.elem.2 b hbA) hap hb1 hnotab hab.symm
    simpa [H, sup_comm] using h
  have hnt : ∀ c ∈ H, NonInnDiag p c J → FieldOn p c J ∨ (p = 3 ∧ IsTD4 3 J) := by
    intro c hcH hnonJ
    have hcA : c ∈ A := hHA hcH
    have hcp : c ^ p = 1 := hpre.elem.2 c hcA
    rcases (i91_holds G p) hp hp2 (L ⊓ Subgroup.centralizer ({d} : Set G)) J c
      hpre.pcomp hpre.chevJ hnonJ.1 hcp hnonJ with hF | ⟨hp3, hD | hT⟩
    · exact Or.inl hF
    · subst hp3
      exact absurd hD ((not_d4_of_linUni_two hc (shape_catalog_of_J hcatJ)).1)
    · exact Or.inr ⟨hp3, hT⟩
  obtain ⟨A₀, hA₀H, hA₀Inn, hcardH, hA₀max⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.T156.t156_split hp hp2 hqJ hpre.chevJ hHnorm hHexp hnt
  have hA₀card : p ≤ Nat.card A₀ := by
    have hle : p ^ 2 ≤ p * Nat.card A₀ := by
      rw [← hHcard]
      exact hcardH
    have hpp : p * p ≤ p * Nat.card A₀ := by simpa [pow_two] using hle
    exact Nat.le_of_mul_le_mul_left hpp hp.pos
  have hnotsub : ¬ A₀ ≤ Subgroup.zpowers b := by
    intro hle
    have hA₀eq : A₀ = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hHcard_b]; omega)
    have hbA₀ : b ∈ A₀ := by rw [hA₀eq]; exact Subgroup.mem_zpowers b
    exact hbInnJ0 (S10.innDiagOn_mono hA₀Inn (Subgroup.zpowers_le.2 hbA₀))
  obtain ⟨c, hcA₀, hc_not_b⟩ := Set.not_subset.1 hnotsub
  have hcH : c ∈ H := hA₀H hcA₀
  have hcA : c ∈ A := hHA hcH
  have hcN_L : c ∈ Subgroup.normalizer (L : Set G) := hpre.norm hcA
  have hcp : c ^ p = 1 := hpre.elem.2 c hcA
  have hdp : d ^ p = 1 := hpre.elem.2 d hdA
  obtain ⟨x, hx, y, hy, hcxy⟩ := (CFSG.mem_sup_of_commute hcommH).1 hcH
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hpi : ¬ (p : ℤ) ∣ i := by
    intro hdvd
    have hai1 : a ^ i = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, horda]
      exact hdvd
    apply hc_not_b
    rw [← hcxy]
    simp [hai1]
  have hcNotInnL : ¬ InnDiagOn p (Subgroup.zpowers c) L := by
    intro hcInn
    have hbjInn : InnDiagOn p (Subgroup.zpowers (b ^ j)) L :=
      S10.innDiagOn_mono hbInn (Subgroup.zpowers_le.2 (Subgroup.zpow_mem_zpowers b j))
    have hcb : c * b ^ j = b ^ j * c :=
      isElemAbelian_commute hpre.elem hcA (Subgroup.zpow_mem _ hbA j)
    have hsupInn : InnDiagOn p (Subgroup.zpowers c ⊔ Subgroup.zpowers (b ^ j)) L :=
      t158_innDiagOn_sup hp hLself hpre.chev2 hcb hcInn hbjInn
    have hai_mem : a ^ i ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers (b ^ j) := by
      have hmem : c * (b ^ j)⁻¹ ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers (b ^ j) :=
        Subgroup.mul_mem _
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
          (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers (b ^ j))))
      have heq : a ^ i = c * (b ^ j)⁻¹ := by
        rw [← hcxy]
        group
      rwa [heq]
    have haiInn : InnDiagOn p (Subgroup.zpowers (a ^ i)) L :=
      S10.innDiagOn_mono hsupInn (Subgroup.zpowers_le.2 hai_mem)
    have hai_ne : a ^ i ≠ 1 := by
      intro h1
      apply hpi
      have hdiv : (orderOf a : ℤ) ∣ i := (orderOf_dvd_iff_zpow_eq_one).2 h1
      rwa [horda] at hdiv
    have hzy : Subgroup.zpowers (a ^ i) = Subgroup.zpowers a :=
      TauCeti.zpowers_eq_zpowers_of_mem_zpowers hp hap hai_ne (Subgroup.zpow_mem_zpowers a i)
    exact hnot (by rwa [← hzy])
  have hfield_c : FieldOn p c L :=
    fieldOn_of_notInnDiag_of_shape hc hp hp2 hLself hpre.chev2 hcatL hcN_L hcp hcNotInnL
  have hcd : c * d = d * c := isElemAbelian_commute hpre.elem hcA hdA
  have hcN_J : c ∈ Subgroup.normalizer (J : Set G) := by
    have hX := CFSG.LocalAnalysis.GLTheoremA.H1431c.normalizer_inf_centralizer hcN_L
      (isElemAbelian_commute hpre.elem hcA hdA)
    simpa [hJlayer] using CFSG.LocalAnalysis.GLTheoremA.S12.mem_normalizer_glaLayer' hX
  have hc1 : c ≠ 1 := fun h1 => hc_not_b (h1 ▸ Subgroup.one_mem _)
  have hd_not_c : d ∉ Subgroup.zpowers c := by
    intro hdc
    have hzy : Subgroup.zpowers d = Subgroup.zpowers c :=
      TauCeti.zpowers_eq_zpowers_of_mem_zpowers hp hcp hpre.d_ne hdc
    exact hcNotInnL (by simpa [hzy] using hdInn)
  have hc_not_d : c ∉ Subgroup.zpowers d := fun hcd' =>
    hcNotInnL (S10.innDiagOn_mono hdInn (Subgroup.zpowers_le.2 hcd'))
  have hfg_c : FGOn p c J := by
    rcases hshapeQ with hQ | hQ
    · exact fgOn_of_fgFldOn hp hp2 (t158FgFldOn_lin p) hLself hpre.chev2 hQ
        hdp hcp hcd.symm hd_not_c hc_not_d hdInn hfield_c hpre.pcomp hcN_J
    · exact fgOn_of_fgFldOn hp hp2
        (t158FgFldOn_of_omegaFld l154OmegaFld_uni p) hLself hpre.chev2 hQ
        hdp hcp hcd.symm hd_not_c hc_not_d hdInn hfield_c hpre.pcomp hcN_J
  have hnonJ_c : NonInnDiag p c J := by
    rcases hfg_c with hF | hG
    · exact MI.field_nonInnDiag_any hpre.pcomp hF
    · exact hG.1
  exact hnonJ_c.2 (S10.innDiagOn_mono hA₀Inn (Subgroup.zpowers_le.2 hcA₀))

theorem t158ClaimLU_holds : T158ClaimLU :=
  t158ClaimLU_of CatDistinct.ctx_holds

end CertsClaim

end CFSG.LocalAnalysis.GLTheoremA.T158

end
