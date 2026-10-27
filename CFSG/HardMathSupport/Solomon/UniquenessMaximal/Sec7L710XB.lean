module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710YBasic
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710XB1
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsB

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {B T I : Subgroup G}

omit [Finite G] in
theorem wOf_le_yOf (B T I : Subgroup G) : wOf B T I ≤ yOf B T I := inf_le_right

abbrev YBar (B T I : Subgroup G) : Type := ↥(yOf B T I) ⧸ GLAPPrimeCore 3 ↥(yOf B T I)

@[expose] noncomputable def sigmaQ (B T I : Subgroup G) : ↥(wOf B T I) →* YBar B T I :=
  (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(yOf B T I))).comp
    (Subgroup.inclusion (wOf_le_yOf B T I))

omit [Finite G] in
theorem mem_core_iff_mem_pOf (B T I : Subgroup G) (y : ↥(yOf B T I)) :
    y ∈ GLAPPrimeCore 3 ↥(yOf B T I) ↔ (y : G) ∈ pOf B T I := by
  constructor
  · intro h
    exact ⟨y, h, rfl⟩
  · rintro ⟨y', hy', hyy⟩
    have : y' = y := Subtype.ext hyy
    exact this ▸ hy'

omit [Finite G] in
theorem sigmaQ_eq_one_iff (B T I : Subgroup G) (w : ↥(wOf B T I)) :
    sigmaQ B T I w = 1 ↔ (w : G) ∈ pOf B T I := by
  rw [← mem_core_iff_mem_pOf B T I ⟨w, wOf_le_yOf B T I w.2⟩]
  exact QuotientGroup.eq_one_iff _

omit [Finite G] in
theorem sigmaQ_le (hf : YFacts B T I) :
    (zOf B T I).subgroupOf (wOf B T I) ≤ (sigmaQ B T I).ker := by
  intro w hw
  rw [MonoidHom.mem_ker, sigmaQ_eq_one_iff]
  exact zOf_le_pOf hf ((Subgroup.mem_subgroupOf).1 hw)

@[expose] noncomputable def psiQ (hf : YFacts B T I) : XQ B T I →* YBar B T I :=
  QuotientGroup.lift _ (sigmaQ B T I) (sigmaQ_le hf)

omit [Finite G] in
theorem psiQ_piQ (hf : YFacts B T I) (w : ↥(wOf B T I)) :
    psiQ hf (piQ B T I w) = sigmaQ B T I w := rfl

theorem psiQ_surjective (hf : YFacts B T I) : Function.Surjective (psiQ hf) := by
  intro z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨p, hp, w, hw, hyw⟩ := exists_mul_wOf hf y.2
  refine ⟨piQ B T I ⟨w, hw⟩, ?_⟩
  have hp' : (⟨p, pOf_le_yOf B T I hp⟩ : ↥(yOf B T I)) ∈ GLAPPrimeCore 3 ↥(yOf B T I) :=
    (mem_core_iff_mem_pOf B T I _).2 hp
  have : y = ⟨p, pOf_le_yOf B T I hp⟩ * ⟨w, wOf_le_yOf B T I hw⟩ := Subtype.ext hyw
  rw [psiQ_piQ]
  change QuotientGroup.mk (⟨w, wOf_le_yOf B T I hw⟩ : ↥(yOf B T I)) = QuotientGroup.mk y
  rw [this, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hp', one_mul]

theorem coprime_ker_psiQ (hf : YFacts B T I) : Nat.Coprime 3 (Nat.card (psiQ hf).ker) := by
  refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun hd =>
    not_three_dvd_card_pOf B T I (hd.trans ?_)
  have h1 : (psiQ hf).ker ≤ ((pOf B T I).subgroupOf (wOf B T I)).map (piQ B T I) := by
    intro x hx
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨w, (Subgroup.mem_subgroupOf).2 ((sigmaQ_eq_one_iff B T I w).1 hx), rfl⟩
  refine (Subgroup.card_dvd_of_le h1).trans ((Subgroup.card_map_dvd _ _).trans ?_)
  have hc : Nat.card (((pOf B T I).subgroupOf (wOf B T I)).map (wOf B T I).subtype) =
      Nat.card ((pOf B T I).subgroupOf (wOf B T I)) :=
    Subgroup.card_map_of_injective (wOf B T I).subtype_injective
  rw [← hc]
  refine Subgroup.card_dvd_of_le ?_
  rintro _ ⟨x, hx, rfl⟩
  exact (Subgroup.mem_subgroupOf).1 hx

theorem glaPPrimeCore_yBar (B T I : Subgroup G) : GLAPPrimeCore 3 (YBar B T I) = ⊥ :=
  glaPPrimeCore_quotient_eq_bot Nat.prime_three

omit [Finite G] in
theorem isSubnormal_of_le_normalizer' {Q : Type*} [Group Q] {C M : Subgroup Q}
    (hMC : M ≤ C) (hn : C ≤ Subgroup.normalizer (M : Set Q)) : IsSubnormal M C :=
  IsSubnormal.step hMC ((Subgroup.normal_subgroupOf_iff_le_normalizer hMC).2 hn)
    (IsSubnormal.refl C)

theorem isQuasisimple_of_isLThreeFour' {X : Type} [Group X] (h : IsLThreeFour X) :
    CFSG.Open.IsQuasisimple X := by
  obtain ⟨K, hK, hKf, hcard, ⟨e⟩⟩ := h
  have hP : IsLThreeFour (StatedProj (StatedSL 3 K)) := ⟨K, hK, hKf, hcard, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hs, a, b, hab⟩ := isSimpleGroup_of_isLThreeFour hP
  have := hs
  have : Group.IsPerfect (StatedProj (StatedSL 3 K)) := by
    refine ⟨?_⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (StatedProj (StatedSL 3 K)))
      with h | h
    · exfalso
      have hmem := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [commutator_def] at h
      rw [h, Subgroup.mem_bot] at hmem
      exact hab (commutatorElement_eq_one_iff_mul_comm.1 hmem)
    · exact h
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv e
    (CFSG.ComponentClassification.Quasisimple.simple_of_perfect _)

theorem not_three_dvd_orderOf_of_mem_pOf {g : G} (hg : g ∈ pOf B T I) : ¬ 3 ∣ orderOf g := by
  intro hd
  have h := orderOf_dvd_natCard (⟨g, hg⟩ : ↥(pOf B T I))
  rw [Subgroup.orderOf_mk] at h
  exact not_three_dvd_card_pOf B T I (hd.trans h)

theorem eq_one_of_mem_pOf {g : G} (hg : g ∈ pOf B T I) (h3 : g ^ 3 = 1) : g = 1 := by
  have h1 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ dvd_rfl) (not_three_dvd_orderOf_of_mem_pOf hg)

omit [Finite G] in
theorem mem_of_pow_three_eq_one {H : Type*} [Group H] (N : Subgroup H) [N.Normal] {b p : H}
    (hb : b ^ 3 = 1) (hp : ¬ 3 ∣ orderOf p) (hbp : b * p ∈ N) : b ∈ N := by
  have h1 : orderOf (QuotientGroup.mk' N b) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hb, map_one])
  have h2 : QuotientGroup.mk' N b = (QuotientGroup.mk' N p)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul]; exact (QuotientGroup.eq_one_iff _).2 hbp)
  rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
  · exact (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h)
  · exfalso
    refine hp ?_
    have h3 : orderOf (QuotientGroup.mk' N p) ∣ orderOf p := orderOf_map_dvd _ _
    rw [h2, orderOf_inv] at h
    exact h ▸ h3

omit [Finite G] in
theorem card_map_of_injOn {A H : Type*} [Group A] [Group H] (S : Subgroup A) (f : A →* H)
    (hf : ∀ a ∈ S, ∀ a' ∈ S, f a = f a' → a = a') : Nat.card (S.map f) = Nat.card S := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun s : S => (⟨f s, s, s.2, rfl⟩ : S.map f))
    ⟨fun s s' hss => Subtype.ext (hf _ s.2 _ s'.2 (congrArg Subtype.val hss)), ?_⟩)
  rintro ⟨_, a, ha, rfl⟩
  exact ⟨⟨a, ha⟩, rfl⟩

theorem bBar_inf_iBar (h : Setup710 B T I) (hf : YFacts B T I) :
    (bX B T I).map (psiQ hf) ⊓ barX 3 (yOf B T I) I =
      ((B ⊓ I).subgroupOf (yOf B T I)).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(yOf B T I))) := by
  have hIn : (I.subgroupOf (yOf B T I)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (I_le_yOf B T I)).2 (y_le_normalizer_I h)
  ext x
  constructor
  · rintro ⟨⟨_, ⟨⟨b, hbW⟩, hb, rfl⟩, rfl⟩, j, hj, hjx⟩
    have hb' : b ∈ B := (Subgroup.mem_subgroupOf).1 hb
    have hbY : b ∈ yOf B T I := wOf_le_yOf B T I hbW
    have hj' : (j : G) ∈ I := (Subgroup.mem_subgroupOf).1 hj
    have h1 : (⟨b, hbY⟩ : ↥(yOf B T I))⁻¹ * j ∈ GLAPPrimeCore 3 ↥(yOf B T I) :=
      QuotientGroup.eq.1 (hjx.trans rfl).symm
    have h2 : b⁻¹ * (j : G) ∈ pOf B T I := (mem_core_iff_mem_pOf B T I _).1 h1
    have hbI : b ∈ I := by
      have := mem_of_pow_three_eq_one (I.subgroupOf (yOf B T I)) (b := ⟨b, hbY⟩)
        (p := ⟨b⁻¹ * (j : G), pOf_le_yOf B T I h2⟩)
        (Subtype.ext (h.bElem.2 b hb'))
        (by
          rw [Subgroup.orderOf_mk]
          exact not_three_dvd_orderOf_of_mem_pOf h2)
        (by
          have : (⟨b, hbY⟩ : ↥(yOf B T I)) * ⟨b⁻¹ * (j : G), pOf_le_yOf B T I h2⟩ = j :=
            Subtype.ext (by simp)
          rw [this]
          exact hj)
      exact (Subgroup.mem_subgroupOf).1 this
    exact ⟨⟨b, hbY⟩, (Subgroup.mem_subgroupOf).2 ⟨hb', hbI⟩, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    have hj' : (j : G) ∈ B ⊓ I := (Subgroup.mem_subgroupOf).1 hj
    refine ⟨⟨_, ⟨⟨j, ?_⟩, ?_, rfl⟩, rfl⟩, ⟨j, ?_, rfl⟩⟩
    · exact b_le_wOf h hj'.1
    · exact (Subgroup.mem_subgroupOf).2 hj'.1
    · exact (Subgroup.mem_subgroupOf).2 hj'.2

theorem card_bBar_inf_iBar (h : Setup710 B T I) (hf : YFacts B T I) :
    Nat.card ↥((bX B T I).map (psiQ hf) ⊓ barX 3 (yOf B T I) I) = 9 := by
  rw [bBar_inf_iBar h hf, card_map_of_injOn]
  · rw [← h.card_bI]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans (B_le_yOf B T I))).toEquiv
  · intro a ha a' ha' haa
    have ha1 : (a : G) ∈ B := ((Subgroup.mem_subgroupOf).1 ha).1
    have ha2 : (a' : G) ∈ B := ((Subgroup.mem_subgroupOf).1 ha').1
    have h1 : a⁻¹ * a' ∈ GLAPPrimeCore 3 ↥(yOf B T I) := QuotientGroup.eq.1 haa
    have h2 : (a : G)⁻¹ * (a' : G) ∈ pOf B T I := (mem_core_iff_mem_pOf B T I _).1 h1
    have h3 : ((a : G)⁻¹ * (a' : G)) ^ 3 = 1 :=
      h.bElem.2 _ (B.mul_mem (B.inv_mem ha1) ha2)
    have := eq_one_of_mem_pOf h2 h3
    exact Subtype.ext (inv_mul_eq_one.1 this)

theorem exists_kX {B T I : Subgroup G} (h : Setup710 B T I) (hf : YFacts B T I) :
    ∃ KX : Subgroup (XQ B T I), GLAPComponent 3 (⊤ : Subgroup (XQ B T I)) KX ∧
      IsLThreeFour (↥KX ⧸ GLAPPrimeCore 3 ↥KX) ∧
      barX 3 (⊤ : Subgroup (XQ B T I)) KX ⊔ barX 3 (⊤ : Subgroup (XQ B T I)) (tX B T I) ⊔
        barX 3 (⊤ : Subgroup (XQ B T I)) (bX B T I) = ⊤ ∧
      Nat.card ↥(barX 3 (⊤ : Subgroup (XQ B T I)) (bX B T I) ⊓
        barX 3 (⊤ : Subgroup (XQ B T I)) KX) = 9 ∧
      ∀ N₁ : Subgroup (XQ B T I),
        barX 3 (⊤ : Subgroup (XQ B T I)) KX ≤ barX 3 (⊤ : Subgroup (XQ B T I)) N₁ →
          (I : Set G) ⊆ (preQ B T I N₁ : Set G) * (pOf B T I : Set G) := by
  obtain ⟨Φ, hΦ⟩ := exists_barX_top_equiv Nat.prime_three (psiQ hf) (psiQ_surjective hf)
    (coprime_ker_psiQ hf) (glaPPrimeCore_yBar B T I)
  have key : ∀ L : Subgroup (XQ B T I), barX 3 (⊤ : Subgroup (XQ B T I)) L =
      (L.map (psiQ hf)).map Φ.symm.toMonoidHom := fun L => by
    rw [← hΦ L, Subgroup.map_map]
    have : Φ.symm.toMonoidHom.comp Φ.toMonoidHom = MonoidHom.id _ := by ext x; simp
    rw [this, Subgroup.map_id]
  have hIsn : IsSubnormal I (yOf B T I) :=
    isSubnormal_of_le_normalizer' (I_le_yOf B T I) (y_le_normalizer_I h)
  have hIn : (I.subgroupOf (yOf B T I)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (I_le_yOf B T I)).2 (y_le_normalizer_I h)
  set Ib : Subgroup (YBar B T I) := barX 3 (yOf B T I) I with hIb
  have hIbn : Ib.Normal := Subgroup.Normal.map hIn _ (QuotientGroup.mk'_surjective _)
  have e4 := quotEquivBarX Nat.prime_three (I_le_yOf B T I) hIsn
  have hqs : CFSG.Open.IsQuasisimple ↥Ib :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e4
      (isQuasisimple_of_isLThreeFour' h.lthree)
  set K : Subgroup (↥(⊤ : Subgroup (XQ B T I)) ⧸ GLAPPrimeCore 3 ↥(⊤ : Subgroup (XQ B T I))) :=
    Ib.map Φ.symm.toMonoidHom with hK
  have hKn : K.Normal := Subgroup.Normal.map hIbn _ Φ.symm.surjective
  have e3 : ↥Ib ≃* ↥K := Subgroup.equivMapOfInjective Ib Φ.symm.toMonoidHom Φ.symm.injective
  have hcomp : IsComponentOf K ⊤ := by
    refine ⟨le_top, ?_, CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e3 hqs⟩
    exact isSubnormal_of_le_normalizer' le_top (by
      rw [Subgroup.normalizer_eq_top_iff.2 hKn])
  obtain ⟨KX, hKX, hbarKX⟩ := exists_glaPComponent_barX_eq (⊤ : Subgroup (XQ B T I)) hcomp
  have hKXmap : KX.map (psiQ hf) = Ib := by
    rw [← hΦ KX, hbarKX, hK, Subgroup.map_map]
    have : Φ.toMonoidHom.comp Φ.symm.toMonoidHom = MonoidHom.id _ := by ext x; simp
    rw [this, Subgroup.map_id]
  refine ⟨KX, hKX, ?_, ?_, ?_, ?_⟩
  · have e1 := quotEquivBarX Nat.prime_three (le_top : KX ≤ ⊤) hKX.2.1
    have e2 : ↥(barX 3 (⊤ : Subgroup (XQ B T I)) KX) ≃* ↥K := MulEquiv.subgroupCongr hbarKX
    exact IsLThreeFour.of_mulEquiv (e4.trans (e3.trans (e2.symm.trans e1.symm))) h.lthree
  · rw [key, key, key, ← Subgroup.map_sup, ← Subgroup.map_sup, hKXmap]
    suffices hs : Ib ⊔ (tX B T I).map (psiQ hf) ⊔ (bX B T I).map (psiQ hf) = ⊤ by
      rw [hs, Subgroup.map_top_of_surjective _ Φ.symm.surjective]
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨i, hi, t, ht, b, hb, hy⟩ := exists_mul_of_mem_yOf h y.2
    have hyy : y = ⟨i, I_le_yOf B T I hi⟩ * ⟨t, T_le_yOf B T I ht⟩ * ⟨b, B_le_yOf B T I hb⟩ :=
      Subtype.ext hy
    have h1 : (QuotientGroup.mk (⟨i, I_le_yOf B T I hi⟩ : ↥(yOf B T I)) : YBar B T I) ∈ Ib :=
      ⟨_, (Subgroup.mem_subgroupOf).2 hi, rfl⟩
    have h2 : (QuotientGroup.mk (⟨t, T_le_yOf B T I ht⟩ : ↥(yOf B T I)) : YBar B T I) ∈
        (tX B T I).map (psiQ hf) :=
      ⟨_, ⟨⟨t, t_le_wOf h ht⟩, (Subgroup.mem_subgroupOf).2 ht, rfl⟩, rfl⟩
    have h3 : (QuotientGroup.mk (⟨b, B_le_yOf B T I hb⟩ : ↥(yOf B T I)) : YBar B T I) ∈
        (bX B T I).map (psiQ hf) :=
      ⟨_, ⟨⟨b, b_le_wOf h hb⟩, (Subgroup.mem_subgroupOf).2 hb, rfl⟩, rfl⟩
    rw [hyy, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left h1))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right h2))) (Subgroup.mem_sup_right h3)
  · rw [key, key, ← Subgroup.map_inf_eq _ _ _ Φ.symm.injective,
      Subgroup.card_map_of_injective Φ.symm.injective, hKXmap]
    exact card_bBar_inf_iBar h hf
  · intro N₁ hN
    have hle : KX.map (psiQ hf) ≤ N₁.map (psiQ hf) := by
      rw [← hΦ KX, ← hΦ N₁]
      exact Subgroup.map_mono hN
    intro i hi
    have hmem : (QuotientGroup.mk (⟨i, I_le_yOf B T I hi⟩ : ↥(yOf B T I)) : YBar B T I) ∈
        N₁.map (psiQ hf) := by
      apply hle
      rw [hKXmap]
      exact ⟨_, (Subgroup.mem_subgroupOf).2 hi, rfl⟩
    obtain ⟨n, hn, hni⟩ := hmem
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective n
    have h1 : (⟨(w : G), wOf_le_yOf B T I w.2⟩ : ↥(yOf B T I))⁻¹ * ⟨i, I_le_yOf B T I hi⟩ ∈
        GLAPPrimeCore 3 ↥(yOf B T I) := QuotientGroup.eq.1 hni
    have h2 : (w : G)⁻¹ * i ∈ pOf B T I := (mem_core_iff_mem_pOf B T I _).1 h1
    exact Set.mem_mul.2 ⟨w, ⟨w, hn, rfl⟩, (w : G)⁻¹ * i, h2, by simp⟩

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710
