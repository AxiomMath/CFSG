module

public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma34
public import CFSG.LocalAnalysis.GLTheoremA.P51.Conj
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.LocalAnalysis.GLTheoremA.ExcClubList

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace S3

theorem pRank_eq_of_bmax {p : ℕ} (hp : p.Prime) {B : Subgroup G} (hB : GLAIsBmax p B) :
    CFSG.Open.pRank p B = GLATwoLocalRank p G := by
  apply le_antisymm
  · unfold CFSG.Open.pRank
    refine csSup_le ⟨GLATwoLocalRank p G, B, le_rfl, hB.1, hB.2.1⟩ ?_
    rintro k ⟨E, hEB, -, hk⟩
    have hdvd : p ^ k ∣ p ^ GLATwoLocalRank p G := by
      rw [← hk, ← hB.2.1]; exact Subgroup.card_dvd_of_le hEB
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd
  · exact CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB.1 hB.2.1

theorem exists_maximal_invariant {A U : Subgroup G} (hU2 : IsPGroup 2 U)
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) :
    ∃ T : Subgroup G, U ≤ T ∧ IsPGroup 2 T ∧ A ≤ Subgroup.normalizer (T : Set G) ∧
      ∀ T' : Subgroup G, IsPGroup 2 T' → A ≤ Subgroup.normalizer (T' : Set G) → T ≤ T' → T' = T := by
  classical
  let 𝒮 : Set (Subgroup G) := {T | U ≤ T ∧ IsPGroup 2 T ∧ A ≤ Subgroup.normalizer (T : Set G)}
  have hfin : 𝒮.Finite := Set.toFinite _
  obtain ⟨T, ⟨hUT, hT2, hAT⟩, hmax⟩ := hfin.exists_maximal ⟨U, le_rfl, hU2, hAU⟩
  exact ⟨T, hUT, hT2, hAT, fun T' hT'2 hAT' hTT' =>
    le_antisymm (hmax ⟨hUT.trans hTT', hT'2, hAT'⟩ hTT') hTT'⟩

theorem exists_cover_component {p : ℕ} (hp : p.Prime) {X L B : Subgroup G} {y : G}
    (hL : GLAPComponent p X L) (hy : CentMod p L y) (hyp : y ^ p = 1)
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) (hBy : ∀ b ∈ B, b * y = y * b) :
    ∃ J : Subgroup G, GLAPComponent p (L ⊓ Subgroup.centralizer ({y} : Set G)) J ∧
      J ⊔ GLAPPrimeCoreOf p L = L ∧ B ≤ Subgroup.normalizer (J : Set G) := by
  have hypg : IsPGroup p (Subgroup.zpowers y) := fun g => by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyp, one_zpow]
  set Y := L ⊓ Subgroup.centralizer ({y} : Set G) with hY
  have hcov : Y ⊔ GLAPPrimeCoreOf p L = L := inf_centralizer_sup_eq_of_centMod hp hypg hy
  obtain ⟨hOY, ⟨e⟩⟩ := cover_facts hp (inf_le_left : Y ≤ L) hcov
  have hYq : CFSG.Open.IsQuasisimple (PQuot p Y) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm
      (isQuasisimple_pQuot_of_glaPComponent hp hL)
  obtain ⟨hJc, huniq, hbar⟩ := glaPLayer_of_isQuasisimple hYq
  refine ⟨GLAPLayer p Y, hJc, ?_, ?_⟩
  · have hJY : GLAPLayer p Y ≤ Y := hJc.1
    have hsupJ : GLAPLayer p Y ⊔ GLAPPrimeCoreOf p Y = Y :=
      sup_glaPPrimeCoreOf_eq_of_barX_eq_top hJY hbar
    apply le_antisymm
    · exact sup_le (hJY.trans inf_le_left) (Subgroup.map_subtype_le _)
    · calc L = Y ⊔ GLAPPrimeCoreOf p L := hcov.symm
        _ = (GLAPLayer p Y ⊔ GLAPPrimeCoreOf p Y) ⊔ GLAPPrimeCoreOf p L := by rw [hsupJ]
        _ ≤ GLAPLayer p Y ⊔ GLAPPrimeCoreOf p L := by
          refine sup_le (sup_le le_sup_left ?_) le_sup_right
          rw [hOY]; exact inf_le_right.trans le_sup_right
  · intro b hb
    have hbC : b ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hBy b hb
    have hbY : b ∈ Subgroup.normalizer (Y : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp only [hY, Subgroup.mem_inf]
      exact and_congr ((Subgroup.mem_normalizer_iff.1 (hBL hb)) x)
        ((Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hbC)) x)
    rw [mem_normalizer_iff_gLBConj_eq]
    have h2 := glaPComponent_gLBConj hJc b
    rw [gLBConj_eq_of_mem_normalizer hbY] at h2
    exact huniq _ h2

theorem inducesInnerMod_of_cover {p : ℕ} (hp : p.Prime) {X L J : Subgroup G}
    (hL : GLAPComponent p X L) (hJL : J ≤ L) (hcov : J ⊔ GLAPPrimeCoreOf p L = L) {c : G}
    (hcL : c ∈ Subgroup.normalizer (L : Set G)) (hcJ : c ∈ Subgroup.normalizer (J : Set G))
    (h : InducesInnerMod p J c) : InducesInnerMod p L c := by
  obtain ⟨l, hlJ, hl⟩ := h
  have hlL : l ∈ L := hJL hlJ
  refine ⟨l, hlL, ?_⟩
  have hOJ : GLAPPrimeCoreOf p J ≤ GLAPPrimeCoreOf p L := by
    rw [(cover_facts hp hJL hcov).1]; exact inf_le_right
  have hOn : L ≤ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) :=
    le_normalizer_glaPPrimeCoreOf p L
  have hcO : c ∈ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) :=
    normalizer_le_normalizer_glaPPrimeCoreOf p L hcL
  have hconjO : ∀ g ∈ L, ∀ o ∈ GLAPPrimeCoreOf p L, g * o * g⁻¹ ∈ GLAPPrimeCoreOf p L :=
    fun g hg o ho => (Subgroup.mem_normalizer_iff.1 (hOn hg) o).1 ho
  let S : Subgroup G :=
    { carrier := {y | y ∈ L ∧ (l⁻¹ * y * l)⁻¹ * (c⁻¹ * y * c) ∈ GLAPPrimeCoreOf p L}
      one_mem' := ⟨L.one_mem, by simpa using (GLAPPrimeCoreOf p L).one_mem⟩
      mul_mem' := by
        rintro a b ⟨ha, hua⟩ ⟨hb, hub⟩
        refine ⟨L.mul_mem ha hb, ?_⟩
        have hB : l⁻¹ * b * l ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hlL) hb) hlL
        have key : (l⁻¹ * (a * b) * l)⁻¹ * (c⁻¹ * (a * b) * c) =
            ((l⁻¹ * b * l)⁻¹ * ((l⁻¹ * a * l)⁻¹ * (c⁻¹ * a * c)) * (l⁻¹ * b * l)) *
              ((l⁻¹ * b * l)⁻¹ * (c⁻¹ * b * c)) := by group
        rw [key]
        refine (GLAPPrimeCoreOf p L).mul_mem ?_ hub
        simpa using hconjO _ (L.inv_mem hB) _ hua
      inv_mem' := by
        rintro a ⟨ha, hua⟩
        refine ⟨L.inv_mem ha, ?_⟩
        have hA : l⁻¹ * a * l ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hlL) ha) hlL
        have key : (l⁻¹ * a⁻¹ * l)⁻¹ * (c⁻¹ * a⁻¹ * c) =
            (l⁻¹ * a * l) * ((l⁻¹ * a * l)⁻¹ * (c⁻¹ * a * c))⁻¹ * (l⁻¹ * a * l)⁻¹ := by group
        rw [key]
        simpa using hconjO _ hA _ ((GLAPPrimeCoreOf p L).inv_mem hua) }
  have hJS : J ≤ S := fun j hj => ⟨hJL hj, hOJ (hl j hj)⟩
  have hOS : GLAPPrimeCoreOf p L ≤ S := fun o ho => ⟨Subgroup.map_subtype_le _ ho, by
    have h1 : l⁻¹ * o * l ∈ GLAPPrimeCoreOf p L := by
      simpa using hconjO _ (L.inv_mem hlL) o ho
    have h2 : c⁻¹ * o * c ∈ GLAPPrimeCoreOf p L := by
      simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hcO) o).1 ho
    exact (GLAPPrimeCoreOf p L).mul_mem ((GLAPPrimeCoreOf p L).inv_mem h1) h2⟩
  have hLS : L ≤ S := by rw [← hcov]; exact sup_le hJS hOS
  exact fun y hy => (hLS hy).2

theorem pcomponent_layer_cen {p : ℕ} (hp : p.Prime) {b y : G} {L J : Subgroup G}
    (hL : GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L)
    (hJ : GLAPComponent p (L ⊓ Subgroup.centralizer ({y} : Set G)) J) :
    GLAPComponent p (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) J ∧
      GLAPComponent p (GLAPLayer p (Subgroup.centralizer ({b} : Set G)) ⊓
        Subgroup.centralizer ({y} : Set G)) J := by
  have h1 : GLAPComponent p (Subgroup.centralizer ({b} : Set G) ⊓
      Subgroup.centralizer ({y} : Set G)) J :=
    glaPComponent_of_isSubnormal' hp (hL.2.1.inf _) hJ
  refine ⟨h1, glaPComponent_of_le hp h1 ?_ ?_⟩
  · exact le_inf ((hJ.1.trans inf_le_left).trans (le_sSup hL)) (hJ.1.trans inf_le_right)
  · exact inf_le_inf_right _ (sSup_le fun K hK => hK.1)

theorem nonempty_pSimple_of_diag {p : ℕ} {M J : Subgroup G}
    (hZJ : Subgroup.center (PQuot p J) = ⊥) (Z : Subgroup (PQuot p M)) [Z.Normal]
    (hZ : Z ≤ Subgroup.center (PQuot p M)) (e : PQuot p J ≃* (PQuot p M ⧸ Z)) :
    Nonempty (PSimple p M ≃* PSimple p J) := by
  have hcenZ : Subgroup.center (PQuot p M) ≤ Z := by
    intro x hx
    have h1 : (QuotientGroup.mk x : PQuot p M ⧸ Z) ∈ Subgroup.center (PQuot p M ⧸ Z) := by
      rw [Subgroup.mem_center_iff]
      intro q
      induction q using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        exact congrArg _ (Subgroup.mem_center_iff.1 hx y)
    have h2 : e.symm (QuotientGroup.mk x) ∈ Subgroup.center (PQuot p J) := by
      rw [Subgroup.mem_center_iff] at h1 ⊢
      intro g
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact h1 (e g)
    rw [hZJ, Subgroup.mem_bot] at h2
    have h3 : (QuotientGroup.mk x : PQuot p M ⧸ Z) = 1 := by
      have := congrArg e h2
      simpa using this
    exact (QuotientGroup.eq_one_iff x).1 h3
  have hZc : Subgroup.center (PQuot p M) = Z := le_antisymm hcenZ hZ
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZc).trans e.symm).trans
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZJ.symm))⟩

private theorem layer_gLBConj' (p : ℕ) (g : G) (X : Subgroup G) :
    GLAPLayer p (GLBConj g X) = GLBConj g (GLAPLayer p X) := by
  refine gLBConj_eq_of_forall_ge (F := GLAPLayer p) (fun g X => ?_) g X
  unfold GLBConj
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (glaPComponent_gLBConj hL g)

theorem mem_normalizer_layerClosure {p : ℕ} {D' J : Subgroup G} {c : G}
    (hcD : c ∈ Subgroup.normalizer ((Subgroup.centralizer (D' : Set G) : Subgroup G) : Set G))
    (hcJ : c ∈ Subgroup.normalizer (J : Set G)) :
    c ∈ Subgroup.normalizer ((layerClosure p D' J : Subgroup G) : Set G) := by
  have hL : c ∈ Subgroup.normalizer
      ((GLAPLayer p (Subgroup.centralizer (D' : Set G)) : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_gLBConj_eq] at hcD ⊢
    rw [← layer_gLBConj', hcD]
  have hcJ' : GLBConj c J = J := gLBConj_eq_of_mem_normalizer hcJ
  rw [mem_normalizer_iff_gLBConj_eq]
  have hle : GLBConj c (layerClosure p D' J) ≤ layerClosure p D' J := by
    have e : GLBConj c (layerClosure p D' J) =
        ⨆ g ∈ GLAPLayer p (Subgroup.centralizer (D' : Set G)), GLBConj c (GLBConj g J) := by
      unfold layerClosure GLBConj
      rw [Subgroup.map_iSup]
      simp_rw [Subgroup.map_iSup]
    rw [e]
    refine iSup₂_le fun g hg => ?_
    have hg' : c⁻¹ * g * c ∈ GLAPLayer p (Subgroup.centralizer (D' : Set G)) := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hL) g).1 hg
      simpa using this
    have e2 : GLBConj c (GLBConj g J) = GLBConj (c⁻¹ * g * c) J := by
      rw [gLBConj_gLBConj]
      have : g * c = c * (c⁻¹ * g * c) := by group
      rw [this, ← gLBConj_gLBConj, hcJ']
    rw [e2]
    exact le_iSup₂ (f := fun g' (_ : g' ∈ GLAPLayer p (Subgroup.centralizer (D' : Set G))) =>
      GLBConj g' J) (c⁻¹ * g * c) hg'
  have hcard : Nat.card (layerClosure p D' J) ≤ Nat.card (GLBConj c (layerClosure p D' J)) := by
    have : Nat.card (GLBConj c (layerClosure p D' J)) = Nat.card (layerClosure p D' J) := by
      unfold GLBConj
      exact Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
    exact this.ge
  exact Subgroup.eq_of_le_of_card_ge hle hcard

private theorem l21_pgroup_inf_eq_bot {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {H Q : Subgroup X} (hH : IsPGroup p H) (hQ : Nat.Coprime p (Nat.card Q)) : H ⊓ Q = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hH.to_le (inf_le_left : H ⊓ Q ≤ H))
  have hdvd : p ^ n ∣ Nat.card Q := by
    rw [← hn]; exact Subgroup.card_dvd_of_le (inf_le_right : H ⊓ Q ≤ Q)
  have h1 : p ^ n = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left n hQ) hdvd
  exact Subgroup.card_eq_one.1 (hn.trans h1)

private theorem l21_isElemAbelian_map {p : ℕ} {H : Type} [Group H] {f : H →* G} {E : Subgroup H}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← ha, ← hb, ← map_mul, ← map_mul, isElemAbelian_commute hE ha' hb']
  · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_pow, hE.2 x' hx', map_one]

private theorem l21_le_normalizer_sup {X : Type} [Group X] {H₁ H₂ Z : Subgroup X}
    (h₁ : ∀ z ∈ Z, ∀ s ∈ H₁, z * s * z⁻¹ ∈ H₁ ⊔ H₂)
    (h₂ : ∀ z ∈ Z, ∀ q ∈ H₂, z * q * z⁻¹ ∈ H₂) :
    Z ≤ Subgroup.normalizer ((H₁ ⊔ H₂ : Subgroup X) : Set X) := by
  have hconj : ∀ z ∈ Z, ∀ t ∈ H₁ ⊔ H₂, z * t * z⁻¹ ∈ H₁ ⊔ H₂ := by
    intro z hz t ht
    have hle : H₁ ⊔ H₂ ≤ (H₁ ⊔ H₂).comap (MulAut.conj z).toMonoidHom :=
      sup_le (fun s hs => h₁ z hz s hs) (fun q hq => Subgroup.mem_sup_right (h₂ z hz q hq))
    exact hle ht
  intro z hz
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hconj z hz h hh, fun hh => ?_⟩
  simpa [mul_assoc] using hconj z⁻¹ (Z.inv_mem hz) _ hh

theorem exists_lift_cent {p : ℕ} (hp : p.Prime) {X K A : Subgroup G} (hK : GLAPComponent p X K)
    (hA : IsPGroup p A) (hAK : A ≤ centModSubgroup p K) (Pbar : Subgroup (PQuot p K))
    (hP : IsElemAbelian p Pbar) :
    ∃ P : Subgroup G, P ≤ K ⊓ Subgroup.centralizer (A : Set G) ∧ IsElemAbelian p P ∧
      Nat.card P = Nat.card Pbar := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hcov : (K ⊓ Subgroup.centralizer (A : Set G)) ⊔ GLAPPrimeCoreOf p K = K :=
    eq_inf_centralizer_sup_of_pgroup hp hA (Subgroup.map_subtype_le _)
      (fun _ hg => normalizer_le_normalizer_glaPPrimeCoreOf p K (hAK hg).1)
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp K))
      (fun _ hy _ hd => (hAK hd).2 _ hy)
  have hQkcard : Nat.card (GLAPPrimeCoreOf p K) = Nat.card (GLAPPrimeCore p ↥K) := by
    unfold GLAPPrimeCoreOf
    rw [Subgroup.card_map_of_injective K.subtype_injective]
  have hQkcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥K)) := by
    rw [← hQkcard]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp K)
  set Qk : Subgroup ↥K := GLAPPrimeCore p ↥K with hQk
  set Ak : Subgroup ↥K := Subgroup.comap K.subtype (Subgroup.centralizer (A : Set G)) with hAk
  set Rk : Subgroup ↥K := Pbar.comap (QuotientGroup.mk' Qk) with hRk
  have hAk_map : Subgroup.map K.subtype Ak = K ⊓ Subgroup.centralizer (A : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hxK, hxC⟩
      exact ⟨⟨x, hxK⟩, hxC, rfl⟩
  have hAQ_top : Ak ⊔ Qk = ⊤ := by
    rw [eq_top_iff]
    intro y _
    apply (Subgroup.mem_map_iff_mem K.subtype_injective).1
    have hmem : K.subtype y ∈ (K ⊓ Subgroup.centralizer (A : Set G)) ⊔ GLAPPrimeCoreOf p K := by
      rw [hcov]; exact y.2
    rw [Subgroup.map_sup, hAk_map]
    exact hmem
  have hRk_card : Nat.card Rk = Nat.card Pbar * Nat.card Qk := by
    have hi : Rk.index = Pbar.index :=
      Subgroup.index_comap_of_surjective Pbar (QuotientGroup.mk'_surjective Qk)
    have hi0 : Pbar.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : Rk.index * Nat.card Rk = Nat.card ↥K := Subgroup.index_mul_card Rk
    have h2 : Pbar.index * Nat.card Pbar = Nat.card (↥K ⧸ Qk) := Subgroup.index_mul_card Pbar
    have h3 : Nat.card ↥K = Nat.card (↥K ⧸ Qk) * Nat.card Qk :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup Qk
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hi0)
    calc Pbar.index * Nat.card Rk = Rk.index * Nat.card Rk := by rw [hi]
      _ = Nat.card ↥K := h1
      _ = Nat.card (↥K ⧸ Qk) * Nat.card Qk := h3
      _ = (Pbar.index * Nat.card Pbar) * Nat.card Qk := by rw [h2]
      _ = Pbar.index * (Nat.card Pbar * Nat.card Qk) := by ring
  have hQk_le : Qk ≤ Rk := by
    intro q hq
    show (QuotientGroup.mk' Qk q : PQuot p K) ∈ Pbar
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff q).2 hq]
    exact Pbar.one_mem
  have hWQ : (Rk ⊓ Ak) ⊔ Qk = Rk := by
    apply le_antisymm
    · exact sup_le inf_le_left hQk_le
    · intro r hr
      have hr' : r ∈ Ak ⊔ Qk := by rw [hAQ_top]; exact Subgroup.mem_top r
      obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hr'
      have hyR : y ∈ Rk := by
        have h := Rk.mul_mem hr (hQk_le (Qk.inv_mem hz))
        simpa using h
      exact Subgroup.mul_mem_sup ⟨hyR, hy⟩ hz
  have hNQk : Rk ⊓ Ak ≤ Subgroup.normalizer (Qk : Set ↥K) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  have hcard1 := card_sup_mul_card_inf_of_le_normalizer hNQk
  rw [sup_comm, hWQ, hRk_card] at hcard1
  have hWcard : Nat.card (Rk ⊓ Ak : Subgroup ↥K) =
      Nat.card Pbar * Nat.card (Qk ⊓ (Rk ⊓ Ak) : Subgroup ↥K) := by
    have hQpos : 0 < Nat.card Qk := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hQpos
    rw [← hcard1]
    ring
  obtain ⟨n, hn⟩ := exists_card_eq_pow_of_isElemAbelian hp hP
  have hdvdW : p ^ n ∣ Nat.card (Rk ⊓ Ak : Subgroup ↥K) :=
    ⟨Nat.card (Qk ⊓ (Rk ⊓ Ak) : Subgroup ↥K), by rw [hWcard, hn]⟩
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime p hdvdW
  set Pk : Subgroup ↥K := F.map (Rk ⊓ Ak).subtype with hPk
  have hPkcard : Nat.card Pk = p ^ n := by
    rw [hPk, Subgroup.card_map_of_injective (Rk ⊓ Ak).subtype_injective, hF]
  have hPkW : Pk ≤ Rk ⊓ Ak := Subgroup.map_subtype_le F
  have hPkp : IsPGroup p Pk := IsPGroup.iff_card.2 ⟨n, hPkcard⟩
  have hPkinf : Pk ⊓ Qk = ⊥ := l21_pgroup_inf_eq_bot hp hPkp hQkcop
  have hPbar : ∀ c ∈ Rk, (QuotientGroup.mk' Qk c : PQuot p K) ∈ Pbar := fun c hc => hc
  have hPkcomm : ∀ a ∈ Pk, ∀ b ∈ Pk, a * b = b * a := by
    intro a ha b hb
    have hc := isElemAbelian_commute hP (hPbar a (hPkW ha).1) (hPbar b (hPkW hb).1)
    have hc' : (QuotientGroup.mk (a * b) : PQuot p K) = QuotientGroup.mk (b * a) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact hc
    have hmem : (a * b)⁻¹ * (b * a) ∈ Pk ⊓ Qk :=
      ⟨Pk.mul_mem (Pk.inv_mem (Pk.mul_mem ha hb)) (Pk.mul_mem hb ha), QuotientGroup.eq.1 hc'⟩
    rw [hPkinf, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem
  have hPkexp : ∀ a ∈ Pk, a ^ p = 1 := by
    intro a ha
    have h1 : QuotientGroup.mk' Qk (a ^ p) = (1 : PQuot p K) := by
      rw [map_pow]
      exact hP.2 _ (hPbar a (hPkW ha).1)
    have h2 : a ^ p ∈ Pk ⊓ Qk := ⟨Pk.pow_mem ha p, (QuotientGroup.eq_one_iff (a ^ p)).1 h1⟩
    rw [hPkinf, Subgroup.mem_bot] at h2
    exact h2
  have hPkel : IsElemAbelian p Pk :=
    ⟨⟨⟨fun a b => Subtype.ext (hPkcomm a a.2 b b.2)⟩⟩, fun x hx => hPkexp x hx⟩
  refine ⟨Pk.map K.subtype, ?_, l21_isElemAbelian_map hPkel, ?_⟩
  · rintro x ⟨a, ha, rfl⟩
    exact ⟨a.2, (hPkW ha).2⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective, hPkcard, hn]

theorem final_count21 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X K S P B₀ : Subgroup G}
    (hK : GLAPComponent p X K) (hZ : Subgroup.center (PQuot p K) = ⊥) (hB₀ : IsElemAbelian p B₀)
    (hB₀K : B₀ ≤ centModSubgroup p K) (hS2 : IsPGroup 2 S) (hSne : S ≠ ⊥)
    (hSc : S ≤ centModSubgroup p K) (hB₀S : B₀ ≤ Subgroup.normalizer (S : Set G))
    (hP : IsElemAbelian p P) (hPK : P ≤ K) (hPB : P ≤ Subgroup.centralizer (B₀ : Set G)) :
    Nat.card P * Nat.card B₀ ≤ p ^ GLATwoLocalRank p G := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hQnd : ¬ p ∣ Nat.card (GLAPPrimeCoreOf p K) := not_dvd_card_glaPPrimeCoreOf hp K
  set Qp : Subgroup G := GLAPPrimeCoreOf p K with hQp
  have hQcop : Nat.Coprime p (Nat.card Qp) := (Nat.Prime.coprime_iff_not_dvd hp).2 hQnd
  have hPN : P ≤ Subgroup.normalizer (Qp : Set G) :=
    hPK.trans (le_normalizer_glaPPrimeCoreOf p K)
  have hB₀N : B₀ ≤ Subgroup.normalizer (Qp : Set G) := fun b hb =>
    normalizer_le_normalizer_glaPPrimeCoreOf p K (hB₀K hb).1
  have hSN : S ≤ Subgroup.normalizer (Qp : Set G) := fun s hs =>
    normalizer_le_normalizer_glaPPrimeCoreOf p K (hSc hs).1
  have hPp : IsPGroup p P := isPGroup_of_isElemAbelian hP
  have hPB0 : P ⊓ B₀ = ⊥ := by
    have hle : P ⊓ B₀ ≤ Qp := by
      rintro x ⟨hxP, hxB⟩
      have hxK : x ∈ K := hPK hxP
      have hxc : x ∈ centModSubgroup p K := hB₀K hxB
      have hcen : (QuotientGroup.mk (⟨x, hxK⟩ : ↥K) : PQuot p K) ∈ Subgroup.center (PQuot p K) := by
        rw [Subgroup.mem_center_iff]
        intro g
        induction g using QuotientGroup.induction_on with
        | H l =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
          refine (Subgroup.mem_map_iff_mem K.subtype_injective).1 ?_
          have hid : K.subtype ((l * ⟨x, hxK⟩)⁻¹ * (⟨x, hxK⟩ * l)) =
              x⁻¹ * ⁅(l : G)⁻¹, x⁆ * x⁻¹⁻¹ := by
            simp only [map_mul, map_inv, Subgroup.coe_subtype, Subgroup.coe_mul,
              Subgroup.coe_inv, commutatorElement_def, inv_inv]
            group
          have h1 : ⁅(l : G)⁻¹, x⁆ ∈ Qp := hxc.2 _ (K.inv_mem l.2)
          have h2 : x⁻¹ * ⁅(l : G)⁻¹, x⁆ * x⁻¹⁻¹ ∈ Qp :=
            (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hB₀N hxB)) _).1 h1
          rw [hid]
          exact h2
      rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
      exact (Subgroup.mem_map_iff_mem K.subtype_injective).2 hcen
    exact le_bot_iff.1 ((le_inf inf_le_left hle).trans
      (l21_pgroup_inf_eq_bot hp hPp hQcop).le)
  have hPBc : P ≤ Subgroup.normalizer (B₀ : Set G) :=
    hPB.trans (Subgroup.centralizer_le_normalizer _)
  have hAel : IsElemAbelian p (P ⊔ B₀) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hP hB₀
      (fun a ha b hb => ((Subgroup.mem_centralizer_iff.1 (hPB ha)) b hb).symm)
  have hcardA : Nat.card (P ⊔ B₀ : Subgroup G) = Nat.card P * Nat.card B₀ := by
    have h := card_sup_mul_card_inf_of_le_normalizer hPBc
    rw [inf_comm, hPB0, Subgroup.card_bot, mul_one, sup_comm] at h
    rw [h, mul_comm]
  have hQS : Nat.card (Qp ⊔ S : Subgroup G) * Nat.card (Qp ⊓ S : Subgroup G) =
      Nat.card Qp * Nat.card S := card_sup_mul_card_inf_of_le_normalizer hSN
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hS2
  have hpS : ¬ p ∣ Nat.card S := by
    intro hd
    rw [ha] at hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have hcopT : Nat.Coprime p (Nat.card (S ⊔ Qp : Subgroup G)) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have hd2 : p ∣ Nat.card (Qp ⊔ S : Subgroup G) := by rwa [sup_comm]
    have hd' : p ∣ Nat.card Qp * Nat.card S :=
      hd2.trans ⟨Nat.card (Qp ⊓ S : Subgroup G), hQS.symm⟩
    rcases (Nat.Prime.dvd_mul hp).1 hd' with h | h
    · exact hQnd h
    · exact hpS h
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hSne (Subgroup.card_eq_one.1 (by rw [ha, pow_zero]))
  have h2S : 2 ∣ Nat.card S := by
    rw [ha]; exact dvd_pow_self 2 ha0
  have h2T : 2 ∣ Nat.card (S ⊔ Qp : Subgroup G) := h2S.trans (Subgroup.card_dvd_of_le le_sup_left)
  have hPT : P ≤ Subgroup.normalizer ((S ⊔ Qp : Subgroup G) : Set G) := by
    refine l21_le_normalizer_sup (fun z hz s hs => ?_) (fun z hz q hq => ?_)
    · have hc : ⁅z, s⁆ ∈ Qp := (hSc hs).2 z (hPK hz)
      have hr : z * s * z⁻¹ = ⁅z, s⁆ * s := by
        rw [commutatorElement_def]; group
      rw [hr]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hs)
    · exact (Subgroup.mem_normalizer_iff.1 (hPN hz) q).1 hq
  have hB₀T : B₀ ≤ Subgroup.normalizer ((S ⊔ Qp : Subgroup G) : Set G) := by
    refine l21_le_normalizer_sup (fun b hb s hs => ?_) (fun b hb q hq => ?_)
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 (hB₀S hb) s).1 hs)
    · exact (Subgroup.mem_normalizer_iff.1 (hB₀N hb) q).1 hq
  have hAT : P ⊔ B₀ ≤ Subgroup.normalizer ((S ⊔ Qp : Subgroup G) : Set G) := sup_le hPT hB₀T
  obtain ⟨S₀, -, hS₀2, hS₀ne, hAS₀, -⟩ :=
    exists_invariant_sylow hp Nat.prime_two (isPGroup_of_isElemAbelian hAel) hAT hcopT h2T
  have hlt := card_le_pow_glaTwoLocalRank hp hAel hS₀ne hS₀2 hAS₀
  rw [hcardA] at hlt
  exact hlt

end S3

private theorem l21_isKGroup_cen (hc : S3Ctx G 3) {x : G} (hx : x ≠ 1) :
    CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) := by
  have h := S3.isKGroup_cen hc.simple hc.nonabelian hc.kProper (E := Subgroup.zpowers x)
    (by simpa using hx)
  rwa [S3.centralizer_zpowers] at h

private theorem l21_rank_le {B : Subgroup G} (hB : GLAIsBmax 3 B) (X : Subgroup G) :
    GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B := by
  rw [S3.pRank_eq_of_bmax Nat.prime_three hB]
  exact glaTwoLocalRank_subgroup_le (by norm_num) X

private theorem l21_normalizes (hc : S3Ctx G 3) (hI112 : I112L227At G) {B : Subgroup G}
    (hB : GLAIsBmax 3 B) {y : G} (hy : y ∈ B) (hy1 : y ≠ 1) {M : Subgroup G}
    (hM : GLAPComponent 3 (Subgroup.centralizer ({y} : Set G)) M)
    (hM27 : catalogIs (PSimple 3 M) (onLie (isL2 27))) :
    B ≤ Subgroup.normalizer (M : Set G) :=
  hI112 _ B M (l21_isKGroup_cen hc hy1) (isElemAbelian_le_centralizer hB.1 hy) hB.1
    (l21_rank_le hB _) hM hM27

private theorem l21_exists_y (hc : S3Ctx G 3) {B B₀ : Subgroup G} (hB : GLAIsBmax 3 B)
    (hB₀B : B₀ ≤ B) (hB₀nc : ¬ IsCyclic B₀) :
    ∃ y ∈ B₀, y ≠ 1 ∧ ∃ S : Subgroup G, S ≤ Subgroup.centralizer ({y} : Set G) ∧ IsPGroup 2 S ∧
      S ≠ ⊥ ∧ B₀ ≤ Subgroup.normalizer (S : Set G) ∧ (⁅B₀, S⁆ : Subgroup G) = S := by
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  have hB₀el : IsElemAbelian 3 B₀ := CFSG.Open.IsElemAbelian.mono hB.1 hB₀B
  have hB₀ne : B₀ ≠ ⊥ := by
    rintro rfl
    exact hB₀nc inferInstance
  obtain ⟨U, hUne, hU2, hBU⟩ := hB.2.2
  obtain ⟨T, hUT, hT2, hB₀T, hTmax⟩ := S3.exists_maximal_invariant hU2 (hB₀B.trans hBU)
  have hTne : T ≠ ⊥ := fun h => hUne (le_bot_iff.1 (h ▸ hUT))
  obtain ⟨-, d₁, d₂, hd₁, -, hd₁1, -, hS₁, -⟩ :=
    (GL83.I_33_1_proved G hc.charTwo 3 hp3 (by norm_num) B₀ T hB₀ne hB₀el hT2 hB₀T
      (Or.inl ⟨hTne, hTmax⟩)).2 B₀ hB₀ne le_rfl hB₀nc
  have hR2 : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer ({d₁} : Set G)) :=
    IsPGroup.to_le hT2 inf_le_left
  have hB₀R : B₀ ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer ({d₁} : Set G) : Subgroup G) : Set G) := by
    intro g hg
    have := S3.mem_normalizer_inf_cen (K := T) (D := Subgroup.zpowers d₁) hB₀el.1
      (Subgroup.zpowers_le.2 hd₁) hg (hB₀T hg)
    rwa [S3.centralizer_zpowers] at this
  obtain ⟨hSR, hB₀S, hSS⟩ := S3.comm_two_group hp3 (by norm_num) hB₀el hR2 hB₀R
  exact ⟨d₁, hd₁, hd₁1, _, (hSR.trans inf_le_right), IsPGroup.to_le hR2 hSR, hS₁, hB₀S, hSS⟩

theorem lemma21 (hc : S3Ctx G 3) (hI112 : I112L227At G) (hData : L227DataAt G)
    (hPump : L227PumpAt G) (h1812 : Input18_3_12) {B : Subgroup G} {b : G} {L : Subgroup G}
    (hB : GLAIsBmax 3 B) (hb : b ∈ B) (hb1 : b ≠ 1)
    (hL : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    (hL27 : catalogIs (PSimple 3 L) (onLie (isL2 27))) :
    B ≤ Subgroup.normalizer (L : Set G) ∧ ∀ c ∈ B, InducesInnerMod 3 L c := by
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := l21_normalizes hc hI112 hB hb hb1 hL hL27
  refine ⟨hBN, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hcB, hcout⟩ := hcon
  have hKX : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({b} : Set G)) := l21_isKGroup_cen hc hb1
  obtain ⟨hZL, -, hidx⟩ := hData _ L hKX hL hL27
  have hidxB := hidx B hB.1 hBN ⟨c, hcB, hcout⟩
  set B₀ : Subgroup G := B ⊓ centModSubgroup 3 L with hB₀def
  have hB₀B : B₀ ≤ B := inf_le_left
  have hB₀L : B₀ ≤ centModSubgroup 3 L := inf_le_right
  have hB₀el : IsElemAbelian 3 B₀ := CFSG.Open.IsElemAbelian.mono hB.1 hB₀B
  have hcardB : Nat.card B = 3 ^ GLATwoLocalRank 3 G := hB.2.1
  have h81 : 3 ^ 4 ≤ Nat.card B := by
    rw [hcardB]
    exact Nat.pow_le_pow_right (by norm_num) hc.rank_ge
  have h9 : 9 ≤ Nat.card B₀ := by omega
  have hB₀nc : ¬ IsCyclic B₀ := S3.not_isCyclic_of_card hp3 hB₀el (by omega)
  obtain ⟨y, hyB₀, hy1, S, hSy, hS2, hSne, hB₀S, hSS⟩ := l21_exists_y hc hB hB₀B hB₀nc
  have hyB : y ∈ B := hB₀B hyB₀
  have hy3 : y ^ 3 = 1 := hB.1.2 y hyB
  have hb3 : b ^ 3 = 1 := hB.1.2 b hb
  have hBy : ∀ x ∈ B, x * y = y * x := fun x hx => isElemAbelian_commute hB.1 hx hyB
  have hyL : CentMod 3 L y := centMod_iff.2 (hB₀L hyB₀)
  obtain ⟨J, hJ, hcov, hBJ⟩ := S3.exists_cover_component hp3 hL hyL hy3 hBN hBy
  have hJL : J ≤ L := hJ.1.trans inf_le_left
  obtain ⟨eJL⟩ := S3.nonempty_pQuot_of_cover hp3 hL hJL hcov
  obtain ⟨fJL⟩ := nonempty_pSimple_congr eJL
  have hJ27 : catalogIs (PSimple 3 J) (onLie (isL2 27)) := (catalogIs_congr fJL).2 hL27
  have hZJ : Subgroup.center (PQuot 3 J) = ⊥ := by
    have h1 := Subgroup.map_center_eq eJL
    rw [hZL] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ eJL.injective).1 h1
  have hcoutJ : ¬ InducesInnerMod 3 J c := fun h =>
    hcout (S3.inducesInnerMod_of_cover hp3 hL hJL hcov (hBN hcB) (hBJ hcB) h)
  obtain ⟨hJbc, hJlay⟩ := S3.pcomponent_layer_cen hp3 hL hJ
  have hKP : CFSG.IsKProper G :=
    CFSG.ComponentClassification.CatalogueKProper.isKProper_of_kProper
      (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1 hc.kProper)
  rcases h1812 G hKP b y hb1 hy1 hb3 hy3 (hBy b hb) J hJlay with
    ⟨hK, hbK⟩ | ⟨M, hM, hbM, -, -, Z, hZn, hZc, ⟨e⟩⟩
  swap
  · exfalso
    obtain ⟨fMJ⟩ := S3.nonempty_pSimple_of_diag hZJ Z hZc e
    have hM27 : catalogIs (PSimple 3 M) (onLie (isL2 27)) := (catalogIs_congr fMJ).2 hJ27
    exact hbM (mem_normalizer_iff_gLBConj_eq.1 (l21_normalizes hc hI112 hB hyB hy1 hM hM27 hb))
  set K : Subgroup G := ⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({y} : Set G)), GLBConj g J
    with hKdef
  have hKeq : layerClosure 3 (Subgroup.zpowers y) J = K := by
    simp only [layerClosure, S3.centralizer_zpowers, hKdef]
  have hBK : B ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    have hxD : x ∈ Subgroup.normalizer
        ((Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) : Subgroup G) : Set G) := by
      rw [S3.centralizer_zpowers]
      exact Subgroup.le_normalizer (isElemAbelian_le_centralizer hB.1 hyB hx)
    have := S3.mem_normalizer_layerClosure (p := 3) (D' := Subgroup.zpowers y) (J := J) (c := x)
      hxD (hBJ hx)
    rwa [hKeq] at this
  have hJK : J ≤ K := by
    have h := le_iSup₂ (f := fun (g : G) (_ : g ∈ GLAPLayer 3 (Subgroup.centralizer ({y} : Set G))) =>
      GLBConj g J) 1 (Subgroup.one_mem _)
    rwa [gLBConj_one] at h
  have hJKb : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set G)) J :=
    glaPComponent_of_le hp3 hJbc
      (le_inf hJK (hJ.1.trans (inf_le_left.trans hL.1)))
      (le_inf inf_le_right (inf_le_left.trans hK.1))
  have hKb : CentMod 3 K b :=
    hPump _ K J b c (l21_isKGroup_cen hc hy1) hK hbK hb3 (hBK hcB) (hBJ hcB)
      (hB.1.2 c hcB) (isElemAbelian_commute hB.1 hb hcB) hJKb hJ27 hcoutJ
  have hcovK : J ⊔ GLAPPrimeCoreOf 3 K = K := by
    refine S3.cover_of_centMod hp3 hK
      (IsPGroup.to_le (CFSG.Open.IsElemAbelian.isPGroup hB.1) (Subgroup.zpowers_le.2 hb))
      (Subgroup.zpowers_le.2 (centMod_iff.1 hKb)) ?_
    rw [S3.centralizer_zpowers]
    exact hJKb
  obtain ⟨eJK⟩ := S3.nonempty_pQuot_of_cover hp3 hK hJK hcovK
  obtain ⟨fJK⟩ := nonempty_pSimple_congr eJK
  have hK27 : catalogIs (PSimple 3 K) (onLie (isL2 27)) := (catalogIs_congr fJK).1 hJ27
  obtain ⟨hZK, ⟨Pbar, hPbar, hPbar27⟩, -⟩ :=
    hData _ K (l21_isKGroup_cen hc hy1) hK hK27
  have hB₀K : B₀ ≤ centModSubgroup 3 K := by
    intro g hg
    have hgB : g ∈ B := hB₀B hg
    have h2 : CentMod 3 J g := S3.centMod_of_le_cen hp3 hJL (hBJ hgB) (centMod_iff.2 (hB₀L hg))
    exact centMod_iff.1 (S3.centMod_of_cover_le hp3 hK hJK hcovK (hBK hgB) (hBJ hgB) h2)
  have hBconj : ∀ s ∈ Subgroup.centralizer ({y} : Set G),
      B ≤ Subgroup.normalizer ((GLBConj s K : Subgroup G) : Set G) := by
    intro s hs
    have hCy : GLBConj s (Subgroup.centralizer ({y} : Set G)) = Subgroup.centralizer ({y} : Set G) :=
      mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hs)
    have hsK : GLAPComponent 3 (Subgroup.centralizer ({y} : Set G)) (GLBConj s K) := by
      have := glaPComponent_gLBConj hK s
      rwa [hCy] at this
    obtain ⟨e⟩ := P51.nonempty_pQuot_gLBConj 3 s K
    obtain ⟨f⟩ := nonempty_pSimple_congr e
    exact l21_normalizes hc hI112 hB hyB hy1 hsK ((catalogIs_congr f).2 hK27)
  have hSS' : (⁅S, B₀⁆ : Subgroup G) = S := by
    rw [Subgroup.commutator_comm]
    exact hSS
  have hSK : S ≤ Subgroup.normalizer (K : Set G) :=
    S3.normalizes_of_comm (A := B₀) (T := S) (K := K)
      (fun t ht => hB₀B.trans (hBconj t (hSy ht))) hSS'.ge
  have hScK : S ≤ centModSubgroup 3 K := S3.le_centModSubgroup_of_comm hB₀K hSK hSS'.ge
  obtain ⟨P, hPle, hPel, hPcard⟩ :=
    S3.exists_lift_cent hp3 hK (CFSG.Open.IsElemAbelian.isPGroup hB₀el) hB₀K Pbar hPbar
  have hfin := S3.final_count21 hp3 (by norm_num) hK hZK hB₀el hB₀K hS2 hSne hScK hB₀S hPel
    (hPle.trans inf_le_left) (hPle.trans inf_le_right)
  rw [hPcard, hPbar27] at hfin
  omega

end CFSG.LocalAnalysis.GLTheoremA
