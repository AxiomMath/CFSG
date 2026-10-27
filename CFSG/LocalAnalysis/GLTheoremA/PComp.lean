module

public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Quasisimple

variable {Q : Type*} [Group Q]

theorem isQuasisimple_nontrivial (hQ : CFSG.Open.IsQuasisimple Q) : Nontrivial Q := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have : Subsingleton (Q ⧸ Subgroup.center Q) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    congr 1
    exact Subsingleton.elim _ _
  have hnt : Nontrivial (Q ⧸ Subgroup.center Q) := hQ.2.toNontrivial
  obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
  exact hab (Subsingleton.elim a b)

omit [Group Q] in
theorem commutatorElement_mul_center_left {Q : Type*} [Group Q] {g h z : Q}
    (hz : z ∈ Subgroup.center Q) : ⁅g * z, h⁆ = ⁅g, h⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  have := Subgroup.mem_center_iff.1 hz h
  calc g * z * h * (z⁻¹ * g⁻¹) * h⁻¹ = g * (h * z) * z⁻¹ * g⁻¹ * h⁻¹ := by
        rw [this]; group
    _ = g * h * g⁻¹ * h⁻¹ := by group

omit [Group Q] in
theorem commutatorElement_mul_center_right {Q : Type*} [Group Q] {g h z : Q}
    (hz : z ∈ Subgroup.center Q) : ⁅g, h * z⁆ = ⁅g, h⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  have := Subgroup.mem_center_iff.1 hz g⁻¹
  calc g * (h * z) * g⁻¹ * (z⁻¹ * h⁻¹) = g * h * (g⁻¹ * z) * z⁻¹ * h⁻¹ := by
        rw [this]; group
    _ = g * h * g⁻¹ * h⁻¹ := by group

theorem le_center_of_normal_of_isQuasisimple (hQ : CFSG.Open.IsQuasisimple Q) {M : Subgroup Q}
    (hM : M.Normal) (hne : M ≠ ⊤) : M ≤ Subgroup.center Q := by
  set π := QuotientGroup.mk' (Subgroup.center Q) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  haveI : (M.map π).Normal := hM.map π hπs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map π) with h | h
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · exfalso
    apply hne
    have hsup : M ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq π M
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hcomm : ⁅(⊤ : Subgroup Q), ⊤⁆ ≤ M := by
      rw [Subgroup.commutator_le]
      intro g _ h _
      have hg : g ∈ M ⊔ Subgroup.center Q := hsup ▸ Subgroup.mem_top g
      have hh : h ∈ M ⊔ Subgroup.center Q := hsup ▸ Subgroup.mem_top h
      rw [← SetLike.mem_coe, Subgroup.mul_normal] at hg hh
      obtain ⟨m₁, hm₁, z₁, hz₁, rfl⟩ := hg
      obtain ⟨m₂, hm₂, z₂, hz₂, rfl⟩ := hh
      rw [commutatorElement_mul_center_left hz₁, commutatorElement_mul_center_right hz₂,
        commutatorElement_def]
      exact M.mul_mem (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem hm₁)) (M.inv_mem hm₂)
    have htop : commutator Q = ⊤ := hQ.1
    exact eq_top_iff.2 (htop ▸ hcomm)

theorem eq_top_of_isComponentOf_of_isQuasisimple [Finite Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {K : Subgroup Q} (hK : IsComponentOf K ⊤) : K = ⊤ := by
  by_contra hne
  obtain ⟨M, hKM, -, hMne, hMn, -⟩ := isSubnormal_exists_normal hK.2.1 hne
  have hMnorm : M.Normal := by
    have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer (le_top : M ≤ ⊤)).1 hMn
    exact Subgroup.normalizer_eq_top_iff.1 (eq_top_iff.2 h1)
  have hMZ := le_center_of_normal_of_isQuasisimple hQ hMnorm hMne
  have hKq : CFSG.Open.IsQuasisimple K := hK.2.2
  have hcomm : commutator K = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _
    rw [Subgroup.mem_centralizer_iff]
    intro b _
    exact Subtype.ext ((Subgroup.mem_center_iff.1 (hMZ (hKM a.2))) b)
  have hKnt : Nontrivial K := isQuasisimple_nontrivial hKq
  have h1 : (⊤ : Subgroup K) = ⊥ := by
    rw [← hcomm]
    exact hKq.1.symm
  obtain ⟨a, b, hab⟩ := hKnt.exists_pair_ne
  apply hab
  have ha : a ∈ (⊥ : Subgroup K) := h1 ▸ Subgroup.mem_top a
  have hb : b ∈ (⊥ : Subgroup K) := h1 ▸ Subgroup.mem_top b
  rw [Subgroup.mem_bot] at ha hb
  rw [ha, hb]

theorem isComponentOf_top_of_isQuasisimple (hQ : CFSG.Open.IsQuasisimple Q) :
    IsComponentOf (⊤ : Subgroup Q) ⊤ :=
  ⟨le_rfl, IsSubnormal.refl _,
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      Subgroup.topEquiv.symm hQ⟩

end Quasisimple

section UniquePComponent

variable {G : Type} [Group G] [Finite G]

theorem glaPComponent_eq_of_isQuasisimple {p : ℕ} {Y K₁ K₂ : Subgroup G}
    (hY : CFSG.Open.IsQuasisimple (↥Y ⧸ GLAPPrimeCore p ↥Y))
    (h₁ : GLAPComponent p Y K₁) (h₂ : GLAPComponent p Y K₂) : K₁ = K₂ :=
  glaPComponent_unique h₁ h₂ (by
    have e1 : barX p Y K₁ = ⊤ := eq_top_of_isComponentOf_of_isQuasisimple hY h₁.2.2.1
    have e2 : barX p Y K₂ = ⊤ := eq_top_of_isComponentOf_of_isQuasisimple hY h₂.2.2.1
    rw [e1, e2])

theorem exists_glaPComponent_of_isQuasisimple {p : ℕ} {Y : Subgroup G}
    (hY : CFSG.Open.IsQuasisimple (↥Y ⧸ GLAPPrimeCore p ↥Y)) :
    ∃ I : Subgroup G, GLAPComponent p Y I ∧ barX p Y I = ⊤ :=
  exists_glaPComponent_barX_eq Y (isComponentOf_top_of_isQuasisimple hY)

theorem glaPLayer_of_isQuasisimple {p : ℕ} {Y : Subgroup G}
    (hY : CFSG.Open.IsQuasisimple (↥Y ⧸ GLAPPrimeCore p ↥Y)) :
    GLAPComponent p Y (GLAPLayer p Y) ∧
      (∀ J : Subgroup G, GLAPComponent p Y J → J = GLAPLayer p Y) ∧
      barX p Y (GLAPLayer p Y) = ⊤ := by
  obtain ⟨I, hI, hIbar⟩ := exists_glaPComponent_of_isQuasisimple hY
  have hall : ∀ J : Subgroup G, GLAPComponent p Y J → J = I := fun J hJ =>
    glaPComponent_eq_of_isQuasisimple hY hJ hI
  have hlayer : GLAPLayer p Y = I := by
    unfold GLAPLayer
    apply le_antisymm
    · exact sSup_le fun J hJ => (hall J hJ).le
    · exact le_sSup hI
  rw [hlayer]
  exact ⟨hI, hall, hIbar⟩

theorem sup_glaPPrimeCoreOf_eq_of_barX_eq_top {p : ℕ} {Y I : Subgroup G} (hIY : I ≤ Y)
    (h : barX p Y I = ⊤) : I ⊔ GLAPPrimeCoreOf p Y = Y := by
  apply le_antisymm (sup_le hIY (Subgroup.map_subtype_le _))
  intro y hy
  obtain ⟨i, hi, hiy⟩ := exists_of_barX_le (J := I) (K := Y) (le_of_eq (h.trans (barX_self p Y).symm).symm) hy hy
  have : y = i * (i⁻¹ * y) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hi) (Subgroup.mem_sup_right hiy)

theorem le_normalizer_of_unique_glaPComponent {p : ℕ} {Y I : Subgroup G}
    (hI : GLAPComponent p Y I) (hall : ∀ J : Subgroup G, GLAPComponent p Y J → J = I) :
    Y ≤ Subgroup.normalizer (I : Set G) := by
  intro y hy
  rw [mem_normalizer_iff_gLBConj_eq]
  have h1 := glaPComponent_gLBConj hI y
  rw [mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hy)] at h1
  exact hall _ h1

theorem mem_of_isPGroup_of_sup_eq {p : ℕ} (hp : p.Prime) {Y I N : Subgroup G}
    (hIY : I ≤ Y) (hYI : Y ≤ Subgroup.normalizer (I : Set G)) (hN : ¬ p ∣ Nat.card N)
    (hsup : I ⊔ N = Y) {y : G} (hy : y ∈ Y) (hyp : IsPGroup p (Subgroup.zpowers y)) :
    y ∈ I := by
  haveI : Fact p.Prime := ⟨hp⟩
  set I' := I.subgroupOf Y with hI'
  haveI : I'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hIY).2 hYI
  have hNY : N ≤ Y := hsup ▸ le_sup_right
  have h1 := card_sup_mul_card_inf_of_le_normalizer (A := I) (B := N) (hNY.trans hYI)
  rw [hsup] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup I'
  have h3 : Nat.card I' = Nat.card I := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIY).toEquiv
  have hIpos : 0 < Nat.card I := Nat.card_pos
  have hdvd : Nat.card (↥Y ⧸ I') ∣ Nat.card N := by
    have key : Nat.card (↥Y ⧸ I') * Nat.card (I ⊓ N : Subgroup G) * Nat.card I =
        Nat.card N * Nat.card I := by
      calc Nat.card (↥Y ⧸ I') * Nat.card (I ⊓ N : Subgroup G) * Nat.card I
          = (Nat.card (↥Y ⧸ I') * Nat.card I') * Nat.card (I ⊓ N : Subgroup G) := by
            rw [h3]; ring
        _ = Nat.card I * Nat.card N := by rw [← h2, h1]
        _ = Nat.card N * Nat.card I := by ring
    exact Dvd.intro _ (Nat.eq_of_mul_eq_mul_right hIpos key)
  have hQp : ¬ p ∣ Nat.card (↥Y ⧸ I') := fun h => hN (h.trans hdvd)
  set π := QuotientGroup.mk' I'
  set y' : ↥Y := ⟨y, hy⟩
  have hy'p : IsPGroup p (Subgroup.zpowers y') := by
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
    obtain ⟨n, hn⟩ := hyp ⟨y ^ k, Subgroup.zpow_mem_zpowers y k⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [← hk]
    simpa using this
  have hord : orderOf (π y') ∣ Nat.card (↥Y ⧸ I') := orderOf_dvd_natCard _
  obtain ⟨n, hn⟩ := (hy'p.map π).exists_card_eq
  have hord2 : orderOf (π y') = p ^ n := by
    rw [← Nat.card_zpowers, ← MonoidHom.map_zpowers, hn]
  have hn0 : n = 0 := by
    by_contra h0
    exact hQp ((dvd_pow_self p h0).trans (hord2 ▸ hord))
  rw [hn0, pow_zero, orderOf_eq_one_iff, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hord2
  exact hord2

theorem glaPComponent_of_isSubnormal' {p : ℕ} (hp : p.Prime) {S X D : Subgroup G}
    (hSX : IsSubnormal S X) (hD : GLAPComponent p S D) : GLAPComponent p X D := by
  obtain ⟨hDS, hsn, hcomp, hmin⟩ := hD
  have hSX' : S ≤ X := isSubnormal_le' hSX
  have hDX : D ≤ X := hDS.trans hSX'
  have hsnX : IsSubnormal D X := isSubnormal_trans' hsn hSX
  refine ⟨hDX, hsnX, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX (C := X) p hsnX
    rwa [barX_self] at this
  · have e : ↥(barX p S D) ≃* ↥(barX p X D) :=
      (quotEquivBarX hp hDS hsn).symm.trans (quotEquivBarX hp hDX hsnX)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hcomp.2.2
  · intro J hJ hJsn heq
    have hJD : J ≤ D := hJ.le
    have hJS : IsSubnormal J S := isSubnormal_of_le_of_le hJsn (hJD.trans hDS) hSX'
    have hcore : D ⊓ GLAPPrimeCoreOf p X ≤ GLAPPrimeCoreOf p S := by
      rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsnX]
      exact glaPPrimeCoreOf_le_of_isSubnormal hp hsn
    refine hmin J hJ hJS ?_
    show barX p S J = barX p S D
    refine le_antisymm (barX_mono p hJD) ?_
    refine barX_le_of_forall (hJD.trans hDS) (fun k hk => ?_)
    obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (X := X) (le_of_eq heq.symm) hk (hDX hk)
    exact ⟨j, hj, hcore ⟨D.mul_mem (D.inv_mem (hJD hj)) hk, hjk⟩⟩

end UniquePComponent

section Covering

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_sup_eq_of_centMod {p : ℕ} (hp : p.Prime) {L : Subgroup G} {a : G}
    (ha : IsPGroup p (Subgroup.zpowers a)) (hCM : CentMod p L a) :
    (L ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ GLAPPrimeCoreOf p L = L := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set O := GLAPPrimeCoreOf p L with hO
  set P := Subgroup.zpowers a with hP
  have hPC : P ≤ centModSubgroup p L := Subgroup.zpowers_le.2 (centMod_iff.1 hCM)
  apply le_antisymm (sup_le inf_le_left (Subgroup.map_subtype_le _))
  intro l hl
  have hmem : ∀ g ∈ P, ∀ o ∈ O, l⁻¹ * (g * (l * o) * g⁻¹) ∈ O := by
    intro g hg o ho
    have hgC := hPC hg
    have h1 : ⁅l⁻¹, g⁆ ∈ O := hgC.2 _ (L.inv_mem hl)
    have h2 : g * o * g⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1
      (normalizer_le_normalizer_glaPPrimeCoreOf p L hgC.1) o).1 ho
    have h3 : l⁻¹ * (g * (l * o) * g⁻¹) = ⁅l⁻¹, g⁆ * (g * o * g⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact O.mul_mem h1 h2
  letI act : MulAction P O :=
    { smul := fun g o => ⟨l⁻¹ * ((g : G) * (l * (o : G)) * (g : G)⁻¹), hmem g g.2 o o.2⟩
      one_smul := fun o => Subtype.ext (show l⁻¹ * (((1 : P) : G) * (l * (o : G)) *
          ((1 : P) : G)⁻¹) = (o : G) by simp)
      mul_smul := fun g h o => Subtype.ext (show l⁻¹ * (((g * h : P) : G) * (l * (o : G)) *
          ((g * h : P) : G)⁻¹) = l⁻¹ * ((g : G) * (l * (l⁻¹ * ((h : G) * (l * (o : G)) *
          (h : G)⁻¹))) * (g : G)⁻¹) by simp only [Subgroup.coe_mul]; group) }
  have hOp : ¬ p ∣ Nat.card O := not_dvd_card_glaPPrimeCoreOf hp L
  obtain ⟨o, ho⟩ := ha.nonempty_fixed_point_of_prime_not_dvd_card O hOp
  have hfa : l⁻¹ * (a * (l * (o : G)) * a⁻¹) = o :=
    congrArg Subtype.val (ho ⟨a, Subgroup.mem_zpowers a⟩)
  have hy : a * (l * (o : G)) * a⁻¹ = l * o := by
    calc a * (l * (o : G)) * a⁻¹ = l * (l⁻¹ * (a * (l * (o : G)) * a⁻¹)) := by group
      _ = l * o := by rw [hfa]
  have hyL : l * (o : G) ∈ L := L.mul_mem hl (Subgroup.map_subtype_le _ o.2)
  have hyC : l * (o : G) ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc l * (o : G) * a = a * (l * (o : G)) * a⁻¹ * a := by rw [hy]
      _ = a * (l * o) := by group
  have hl' : l = (l * (o : G)) * (o : G)⁻¹ := by group
  rw [hl']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hyL, hyC⟩)
    (Subgroup.mem_sup_right (O.inv_mem o.2))

theorem cover_facts {p : ℕ} (hp : p.Prime) {I K : Subgroup G} (hIK : I ≤ K)
    (hsup : I ⊔ GLAPPrimeCoreOf p K = K) :
    GLAPPrimeCoreOf p I = I ⊓ GLAPPrimeCoreOf p K ∧ Nonempty (PQuot p I ≃* PQuot p K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set f : ↥I →* PQuot p K :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥K)).comp (Subgroup.inclusion hIK) with hf
  have hIO : I ≤ Subgroup.normalizer (GLAPPrimeCoreOf p K : Set G) :=
    hIK.trans (le_normalizer_glaPPrimeCoreOf p K)
  have hfs : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H l =>
      have hl : (l : G) ∈ (I ⊔ GLAPPrimeCoreOf p K : Subgroup G) := hsup.symm ▸ l.2
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right I _ hIO] at hl
      obtain ⟨y, hy, o, ho, hyo⟩ := Set.mem_mul.mp hl
      refine ⟨⟨y, hy⟩, ?_⟩
      rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      obtain ⟨o', ho', ho'eq⟩ := ho
      have : (Subgroup.inclusion hIK ⟨y, hy⟩)⁻¹ * l = o' := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
        calc y⁻¹ * (l : G) = y⁻¹ * (y * o) := by rw [hyo]
          _ = o := by group
          _ = (o' : G) := ho'eq.symm
      rw [this]
      exact ho'
  have hkerI : ∀ y : ↥I, y ∈ f.ker ↔ (y : G) ∈ GLAPPrimeCoreOf p K := by
    intro y
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨o, ho, hoeq⟩
      have : Subgroup.inclusion hIK y = o := Subtype.ext hoeq.symm
      rw [this]
      exact ho
  have hcop : Nat.Coprime p (Nat.card f.ker) := by
    have hle : f.ker.map (Subgroup.inclusion hIK) ≤ GLAPPrimeCore p ↥K := by
      rintro _ ⟨y, hy, rfl⟩
      have : f y = 1 := hy
      rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    have hcard : Nat.card (f.ker.map (Subgroup.inclusion hIK)) = Nat.card f.ker :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hIK)
    rw [← hcard]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
      CFSG.pPrimeCore_coprime_card
  have hker : f.ker = GLAPPrimeCore p ↥I := by
    apply le_antisymm
    · exact le_sSup ⟨inferInstance, hcop⟩
    · have hmap := glaPPrimeCore_map_of_surjective hp f hfs hcop
      have hbot : GLAPPrimeCore p (PQuot p K) = ⊥ := by
        have h1 := glaPPrimeCore_map_of_surjective hp (QuotientGroup.mk' (GLAPPrimeCore p ↥K))
          (QuotientGroup.mk'_surjective _) (by
            rw [QuotientGroup.ker_mk']
            exact CFSG.pPrimeCore_coprime_card)
        rw [← h1]
        exact (Subgroup.map_eq_bot_iff _).2 (by rw [QuotientGroup.ker_mk'])
      rw [hbot, Subgroup.map_eq_bot_iff] at hmap
      exact hmap
  refine ⟨?_, ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfs)⟩⟩
  ext y
  constructor
  · rintro ⟨y', hy', rfl⟩
    have hy'' : y' ∈ f.ker := hker ▸ hy'
    exact ⟨y'.2, (hkerI y').1 hy''⟩
  · rintro ⟨hyI, hyO⟩
    have hk : (⟨y, hyI⟩ : ↥I) ∈ f.ker := (hkerI ⟨y, hyI⟩).2 hyO
    exact ⟨⟨y, hyI⟩, hker ▸ hk, rfl⟩

theorem inf_centralizer_quot_facts {p : ℕ} (hp : p.Prime) {L : Subgroup G} {a : G}
    (ha : IsPGroup p (Subgroup.zpowers a)) (hCM : CentMod p L a) :
    Nonempty ((↥(L ⊓ Subgroup.centralizer ({a} : Set G)) ⧸
      GLAPPrimeCore p ↥(L ⊓ Subgroup.centralizer ({a} : Set G))) ≃* PQuot p L) ∧
    GLAPPrimeCoreOf p (L ⊓ Subgroup.centralizer ({a} : Set G)) ≤ GLAPPrimeCoreOf p L := by
  obtain ⟨h1, h2⟩ := cover_facts hp inf_le_left (inf_centralizer_sup_eq_of_centMod hp ha hCM)
  exact ⟨h2, h1 ▸ inf_le_right⟩

theorem isQuasisimple_quot_inf_centralizer {p : ℕ} (hp : p.Prime) {L : Subgroup G} {a : G}
    (hL : CFSG.Open.IsQuasisimple (PQuot p L)) (ha : IsPGroup p (Subgroup.zpowers a))
    (hCM : CentMod p L a) :
    CFSG.Open.IsQuasisimple (↥(L ⊓ Subgroup.centralizer ({a} : Set G)) ⧸
      GLAPPrimeCore p ↥(L ⊓ Subgroup.centralizer ({a} : Set G))) := by
  obtain ⟨⟨e⟩, -⟩ := inf_centralizer_quot_facts hp ha hCM
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hL

theorem isQuasisimple_pQuot_of_glaPComponent {p : ℕ} (hp : p.Prime) {X L : Subgroup G}
    (hL : GLAPComponent p X L) : CFSG.Open.IsQuasisimple (PQuot p L) :=
  CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
    (quotEquivBarX hp hL.1 hL.2.1).symm hL.2.2.1.2.2

theorem glaPLayer_inf_centralizer {p : ℕ} (hp : p.Prime) {X L : Subgroup G} {a : G}
    (hL : GLAPComponent p X L) (ha : IsPGroup p (Subgroup.zpowers a)) (hCM : CentMod p L a) :
    GLAPComponent p (L ⊓ Subgroup.centralizer ({a} : Set G))
        (GLAPLayer p (L ⊓ Subgroup.centralizer ({a} : Set G))) ∧
      (∀ J : Subgroup G, GLAPComponent p (L ⊓ Subgroup.centralizer ({a} : Set G)) J →
        J = GLAPLayer p (L ⊓ Subgroup.centralizer ({a} : Set G))) ∧
      L ⊓ Subgroup.centralizer ({a} : Set G) ≤
        Subgroup.normalizer (GLAPLayer p (L ⊓ Subgroup.centralizer ({a} : Set G)) : Set G) ∧
      (∀ y ∈ L ⊓ Subgroup.centralizer ({a} : Set G), IsPGroup p (Subgroup.zpowers y) →
        y ∈ GLAPLayer p (L ⊓ Subgroup.centralizer ({a} : Set G))) ∧
      GLAPLayer p (L ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ GLAPPrimeCoreOf p L = L ∧
      Nonempty (PQuot p (GLAPLayer p (L ⊓ Subgroup.centralizer ({a} : Set G))) ≃* PQuot p L) := by
  set Y := L ⊓ Subgroup.centralizer ({a} : Set G) with hY
  set I := GLAPLayer p Y with hI
  have hLq := isQuasisimple_pQuot_of_glaPComponent hp hL
  have hYq := isQuasisimple_quot_inf_centralizer hp hLq ha hCM
  obtain ⟨⟨e⟩, hOY⟩ := inf_centralizer_quot_facts hp ha hCM
  obtain ⟨hIc, hall, hIbar⟩ := glaPLayer_of_isQuasisimple hYq
  have hIY : I ≤ Y := hIc.1
  have hsupY : I ⊔ GLAPPrimeCoreOf p Y = Y := sup_glaPPrimeCoreOf_eq_of_barX_eq_top hIY hIbar
  have hnorm := le_normalizer_of_unique_glaPComponent hIc hall
  have hsupL : Y ⊔ GLAPPrimeCoreOf p L = L := inf_centralizer_sup_eq_of_centMod hp ha hCM
  refine ⟨hIc, hall, hnorm, fun y hy hyp => mem_of_isPGroup_of_sup_eq hp hIY hnorm
    (not_dvd_card_glaPPrimeCoreOf hp Y) hsupY hy hyp, ?_, ?_⟩
  · apply le_antisymm (sup_le (hIY.trans inf_le_left) (Subgroup.map_subtype_le _))
    calc L = Y ⊔ GLAPPrimeCoreOf p L := hsupL.symm
      _ = (I ⊔ GLAPPrimeCoreOf p Y) ⊔ GLAPPrimeCoreOf p L := by rw [hsupY]
      _ ≤ I ⊔ GLAPPrimeCoreOf p L := sup_le (sup_le le_sup_left (hOY.trans le_sup_right))
          le_sup_right
  · have e1 : PQuot p I ≃* ↥(barX p Y I) := quotEquivBarX hp hIY hIc.2.1
    rw [hIbar] at e1
    exact ⟨(e1.trans Subgroup.topEquiv).trans e⟩

end Covering

end CFSG.LocalAnalysis.GLTheoremA
