module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4TCore
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S9.L94Quot
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Tools
public import CFSG.HardMathSupport.Solomon.Coordinator.L5Conj

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4T

open CFSG.Open

section Lift

theorem card_comap_of_surjective {X Q : Type} [Group X] [Group Q] [Finite X] [Finite Q]
    (f : X →* Q) (hf : Function.Surjective f) (L : Subgroup Q) :
    Nat.card (L.comap f) = Nat.card L * Nat.card f.ker := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (L.comap f)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup L
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have h4 : Nat.card (X ⧸ f.ker) = Nat.card Q :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  have h5 : Nat.card (X ⧸ L.comap f) = Nat.card (Q ⧸ L) := Subgroup.index_comap_of_surjective L hf
  have hpos : 0 < Nat.card (Q ⧸ L) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc Nat.card (Q ⧸ L) * Nat.card (L.comap f)
      = Nat.card (X ⧸ L.comap f) * Nat.card (L.comap f) := by rw [h5]
    _ = Nat.card X := h1.symm
    _ = Nat.card (X ⧸ f.ker) * Nat.card f.ker := h3
    _ = Nat.card Q * Nat.card f.ker := by rw [h4]
    _ = Nat.card (Q ⧸ L) * Nat.card L * Nat.card f.ker := by rw [h2]
    _ = Nat.card (Q ⧸ L) * (Nat.card L * Nat.card f.ker) := Nat.mul_assoc _ _ _

theorem exists_lift_isElemAbelian {X Q : Type} [Group X] [Group Q] [Finite X] [Finite Q]
    (π : X →* Q) (hπs : Function.Surjective π) (hO : Nat.Coprime 3 (Nat.card π.ker))
    {P : Subgroup Q} (hP : IsElemAbelian 3 P) :
    ∃ K : Subgroup X, IsElemAbelian 3 K ∧ Nat.card K = Nat.card P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQc : Nat.card (P.comap π) = Nat.card P * Nat.card π.ker := card_comap_of_surjective π hπs P
  obtain ⟨a, ha⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hP
  have hdvd : 3 ^ a ∣ Nat.card (P.comap π) := by
    rw [hQc, ha]
    exact dvd_mul_right _ _
  obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  obtain ⟨K, hKle, hKc⟩ : ∃ K : Subgroup X, K ≤ P.comap π ∧ Nat.card K = 3 ^ a :=
    ⟨K₀.map (P.comap π).subtype, Subgroup.map_subtype_le K₀, by
      rw [Subgroup.card_map_of_injective (P.comap π).subtype_injective, hK₀]⟩
  have hbot : K ⊓ π.ker = ⊥ := by
    have h1 : Nat.card (K ⊓ π.ker : Subgroup X) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left a hO)
        (by rw [← hKc]; exact Subgroup.card_dvd_of_le inf_le_left)
        (Subgroup.card_dvd_of_le inf_le_right)
    exact Subgroup.card_eq_one.1 h1
  have hinj : ∀ x ∈ K, ∀ y ∈ K, π x = π y → x = y := by
    intro x hx y hy hxy
    have hmem : x⁻¹ * y ∈ K ⊓ π.ker := by
      refine Subgroup.mem_inf.2 ⟨K.mul_mem (K.inv_mem hx) hy, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    rw [hbot, Subgroup.mem_bot] at hmem
    exact inv_mul_eq_one.1 hmem
  have hKP : K.map π ≤ P := Subgroup.map_le_iff_le_comap.2 hKle
  have hKel : IsElemAbelian 3 K := by
    have hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
      intro a ha b hb
      apply hinj _ (K.mul_mem ha hb) _ (K.mul_mem hb ha)
      rw [map_mul, map_mul]
      exact hP.comm (hKP (Subgroup.mem_map_of_mem π ha)) (hKP (Subgroup.mem_map_of_mem π hb))
    refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
    apply hinj _ (K.pow_mem hx 3) _ K.one_mem
    rw [map_pow, map_one]
    exact hP.2 _ (hKP (Subgroup.mem_map_of_mem π hx))
  exact ⟨K, hKel, by rw [hKc, ha]⟩

theorem card_le_of_quot_even {G : Type} [Group G] [Finite G] {C : Subgroup G}
    (heven : 2 ∣ Nat.card (GLAPPrimeCoreOf 3 C))
    {P : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C)} (hP : IsElemAbelian 3 P) :
    Nat.card P ≤ 3 ^ GLATwoLocalRank 3 G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : Nat.Coprime 3 (Nat.card (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pPrimeCore_coprime_card
  obtain ⟨K, hKel, hKc⟩ := exists_lift_isElemAbelian (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C))
    (QuotientGroup.mk'_surjective _) hO hP
  have hK' : IsElemAbelian 3 (K.map C.subtype) :=
    CFSG.LocalAnalysis.GLTheoremA.S9.l94t_isElemAbelian_map C.subtype hKel
  have hY3 : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 C) :=
    CFSG.LocalAnalysis.GLTheoremB.not_dvd_card_glaPPrimeCoreOf Nat.prime_three C
  have hKY : K.map C.subtype ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 C : Subgroup G) : Set G) := by
    have h1 : K ≤ Subgroup.normalizer ((GLAPPrimeCore 3 ↥C : Subgroup ↥C) : Set ↥C) := by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    intro y hy
    obtain ⟨k, hk, rfl⟩ := hy
    exact Subgroup.le_normalizer_map C.subtype (Subgroup.mem_map_of_mem _ (h1 hk))
  obtain ⟨R, ⟨S, rfl⟩, -, hQR⟩ :=
    CFSG.ABGLocalTools.exists_invariant_isSylowOf_ge_of_coprime (q := 3) (r := 2)
      Nat.prime_three Nat.prime_two (isPGroup_of_isElemAbelian hK') hKY hY3 bot_le
      IsPGroup.of_bot (fun g _ => Subgroup.mem_normalizer_iff.2 fun h => by
        simp only [SetLike.mem_coe, Subgroup.mem_bot]
        constructor <;> intro hh <;> simp_all)
  have hS : (S : Subgroup (GLAPPrimeCoreOf 3 C)) ≠ ⊥ := S.ne_bot_of_dvd_card heven
  have := card_le_pow_glaTwoLocalRank Nat.prime_three hK' ?_ (S.isPGroup'.map _) hQR
  · rw [Subgroup.card_map_of_injective C.subtype_injective, hKc] at this
    exact this
  · intro h
    exact hS ((Subgroup.map_eq_bot_iff_of_injective _ (GLAPPrimeCoreOf 3 C).subtype_injective).1 h)

end Lift


section Wrapper

open scoped commutatorElement

open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S9

@[expose] def D4TwoNormalizes (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X B L : Subgroup G), CFSG.Open.IsKGroup ↥X → IsElemAbelian 3 B → B ≤ X →
    GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B → GLAPComponent 3 X L →
    catalogIs (PSimple 3 L) S9.isD4two → B ≤ Subgroup.normalizer (L : Set G)

@[expose] def D4TwoFactsAt : Prop :=
  ∀ (K : Type) [Group K] [Finite K], catalogIs K S9.isD4two → D4TwoFacts K

theorem catalogIs_mono' {S : Type} [Group S] {Q Q' : TauCeti.CFSGIndex → Prop}
    (hQ : ∀ i, Q i → Q' i) (h : catalogIs S Q) : catalogIs S Q' := by
  obtain ⟨i, hi, f⟩ := h
  exact ⟨i, hQ i hi, f⟩

variable {G : Type} [Group G] [Finite G]

theorem i117At_of_facts (hR : Rank23At G) (hF : D4TwoFactsAt) (h112 : D4TwoNormalizes G) :
    I117At G := by
  classical
  intro B x L hBmax hess hKG hcomp hBL hD4 b hb
  by_contra hbn
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  have hBel : IsElemAbelian 3 B := hBmax.1
  have hBcard : Nat.card B = 3 ^ GLATwoLocalRank 3 G := hBmax.2.1
  have hxB : x ∈ B := hess.1
  have hBC : B ≤ C := isElemAbelian_le_centralizer hBel hxB
  have hLC : L ≤ C := hcomp.1
  have hLsn : IsSubnormal L C := hcomp.2.1
  have hD4' : catalogIs (PSimple 3 L) S9.isList94 :=
    catalogIs_mono' (fun i hi => Or.inr (Or.inr (Or.inl hi))) hD4
  have hZ : Subgroup.center (PQuot 3 L) = ⊥ := (hR C L hcomp hD4').1
  set Kb : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C) := barX 3 C L with hKb
  set Bb : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C) := barX 3 C B with hBb
  let e : PQuot 3 L ≃* ↥Kb := quotEquivBarX hp3 hLC hLsn
  have e0 : PSimple 3 L ≃* PQuot 3 L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hcat : catalogIs ↥Kb S9.isD4two := (catalogIs_congr (e0.trans e)).1 hD4
  haveI : Finite ↥Kb := inferInstance
  have hFK : D4TwoFacts ↥Kb := hF ↥Kb hcat
  have hKc : ∀ k ∈ Kb, (∀ y ∈ Kb, y * k = k * y) → k = 1 := by
    intro k hk hcomm
    obtain ⟨q, hq⟩ := e.surjective ⟨k, hk⟩
    have hqc : q ∈ Subgroup.center (PQuot 3 L) := by
      rw [Subgroup.mem_center_iff]
      intro q'
      apply e.injective
      apply Subtype.ext
      simp only [map_mul, Subgroup.coe_mul]
      rw [hq]
      exact hcomm _ (e q').2
    rw [hZ, Subgroup.mem_bot] at hqc
    subst hqc
    have := congrArg Subtype.val hq
    simpa using this.symm
  have hBO : B ⊓ GLAPPrimeCoreOf 3 C = ⊥ := by
    have hOcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 C)) :=
      (Nat.Prime.coprime_iff_not_dvd hp3).2 (not_dvd_card_glaPPrimeCoreOf hp3 C)
    have hcopB : Nat.Coprime (Nat.card B) (Nat.card (GLAPPrimeCoreOf 3 C)) := by
      rw [hBcard]
      exact Nat.Coprime.pow_left _ hOcop
    have h1 := Nat.eq_one_of_dvd_coprimes hcopB (Subgroup.card_dvd_of_le inf_le_left)
      (Subgroup.card_dvd_of_le inf_le_right)
    exact Subgroup.card_eq_one.1 h1
  have hBbel : IsElemAbelian 3 Bb := l94t_isElemAbelian_barX hBel hBC
  have hBbcard : Nat.card Bb = Nat.card B := l94t_card_barX hBC hBO
  have hBbK : Bb ≤ Subgroup.normalizer (Kb : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) :=
    l94t_barX_le_normalizer (p := 3) hLC hBL
  have hbC : b ∈ C := hBC hb
  have hout : ∃ b' ∈ Bb, ∀ k ∈ Kb, ¬ ∀ y ∈ Kb, b' * y * b'⁻¹ = k * y * k⁻¹ := by
    refine ⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨b, hbC⟩,
      ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 hb, rfl⟩, fun k hk hall => hbn ?_⟩
    obtain ⟨q, hq⟩ := e.surjective ⟨k, hk⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨l, l.2, fun y hy => ?_⟩
    have hbN : b ∈ Subgroup.normalizer (L : Set G) := hBL hb
    have hbyb : b⁻¹ * y * b ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hbN) y).1 hy
      simpa using this
    have hlyl : (l : G)⁻¹ * y * (l : G) ∈ L := L.mul_mem (L.mul_mem (L.inv_mem l.2) hy) l.2
    set π : ↥C →* ↥C ⧸ GLAPPrimeCore 3 ↥C := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) with hπ
    have hz : π ⟨b⁻¹ * y * b, hLC hbyb⟩ ∈ Kb := ⟨⟨b⁻¹ * y * b, hLC hbyb⟩,
      Subgroup.mem_subgroupOf.2 hbyb, rfl⟩
    have hmain := hall _ hz
    have hbbar : π ⟨b, hbC⟩ * π ⟨b⁻¹ * y * b, hLC hbyb⟩ * (π ⟨b, hbC⟩)⁻¹ = π ⟨y, hLC hy⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp [mul_assoc]
    have hkπ : k = π ⟨l, hLC l.2⟩ := by
      have h : ((e (QuotientGroup.mk l) : ↥Kb) : ↥C ⧸ GLAPPrimeCore 3 ↥C) = k := congrArg Subtype.val hq
      rw [← h]
      rfl
    have h1 : π ⟨y, hLC hy⟩ = k * π ⟨b⁻¹ * y * b, hLC hbyb⟩ * k⁻¹ := by
      rw [← hbbar]
      exact hmain
    have h2 : π ⟨b⁻¹ * y * b, hLC hbyb⟩ = π ⟨(l : G)⁻¹ * y * l, hLC hlyl⟩ := by
      have h6 : π ⟨(l : G)⁻¹ * y * l, hLC hlyl⟩ =
          (π ⟨l, hLC l.2⟩)⁻¹ * π ⟨y, hLC hy⟩ * π ⟨l, hLC l.2⟩ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        exact congrArg π (Subtype.ext (by simp [mul_assoc]))
      rw [h6, h1, ← hkπ]
      group
    have h3 : (QuotientGroup.mk ⟨(l : G)⁻¹ * y * l, hlyl⟩ : PQuot 3 L) =
        QuotientGroup.mk ⟨b⁻¹ * y * b, hbyb⟩ := by
      apply e.injective
      apply Subtype.ext
      exact h2.symm
    have ha : ((l : G)⁻¹ * y * l)⁻¹ * (b⁻¹ * y * b) ∈ L :=
      L.mul_mem (L.inv_mem hlyl) hbyb
    refine (l94t_mk_eq_one_iff (p := 3) (X := L) ha).1 ?_
    have h7 : (⟨((l : G)⁻¹ * y * l)⁻¹ * (b⁻¹ * y * b), ha⟩ : ↥L) =
        (⟨(l : G)⁻¹ * y * l, hlyl⟩ : ↥L)⁻¹ * ⟨b⁻¹ * y * b, hbyb⟩ := Subtype.ext (by simp)
    rw [h7, map_mul, map_inv]
    change (QuotientGroup.mk ⟨(l : G)⁻¹ * y * l, hlyl⟩ : PQuot 3 L)⁻¹ *
      QuotientGroup.mk ⟨b⁻¹ * y * b, hbyb⟩ = 1
    rw [h3]
    simp
  have hBrank : GLATwoLocalRank 3 G ≤ CFSG.Open.pRank 3 B :=
    CFSG.SectionRank.le_pRank Nat.prime_three.one_lt (le_refl B) hBel hBcard
  have hcase : (∀ P : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C), IsElemAbelian 3 P →
        Nat.card P ≤ Nat.card Bb) ∨
      ((∀ P W : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C), IsElemAbelian 3 P → IsPGroup 2 W → W ≠ ⊥ →
          P ≤ Subgroup.normalizer (W : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) → Nat.card P ≤ Nat.card Bb) ∧
        ∃ T : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C), IsPGroup 2 T ∧ T ≠ ⊥ ∧
          Bb ≤ Subgroup.normalizer (T : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) ∧
          T ≤ Subgroup.normalizer (Kb : Set (↥C ⧸ GLAPPrimeCore 3 ↥C))) := by
    by_cases hodd : Odd (Nat.card (GLAPPrimeCoreOf 3 C))
    · right
      refine ⟨fun P W hP hW2 hWne hPW => ?_, ?_⟩
      · have := l94_card_le_of_quot (C := C) hP hW2 hWne hPW
        rw [hBbcard, hBcard]
        exact this
      · obtain ⟨-, -, T₀, hT₀C, hT₀2, hBT₀, hne, -⟩ := hess
        obtain ⟨hTT₀, hT'2, hT'B, -⟩ := l94t_commutator_facts hBel hT₀2 hBT₀
        have hT'X : ⁅T₀, B⁆ ≤ C := hTT₀.trans hT₀C
        have hTN : ⁅T₀, B⁆ ≤ Subgroup.normalizer (L : Set G) := by
          refine Subgroup.commutator_le.2 fun t ht b' hb' => ?_
          have htC : t ∈ C := hT₀C ht
          have hconj : GLAPComponent 3 C (GLBConj t L) :=
            CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_gLBConj_of_mem hcomp htC
          have hconjcat : catalogIs (PSimple 3 (GLBConj t L)) S9.isD4two :=
            CFSG.LocalAnalysis.GLTheoremA.S8.L84.catalogIs_pSimple_conj t hD4
          have hBn : B ≤ Subgroup.normalizer ((GLBConj t L : Subgroup G) : Set G) :=
            h112 C B (GLBConj t L) hKG hBel hBC
              ((CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le hp3 C).trans
                hBrank) hconj hconjcat
          have h1 : t * b' * t⁻¹ ∈ Subgroup.normalizer (L : Set G) := by
            rw [Subgroup.mem_normalizer_iff]
            intro z
            have h2 := Subgroup.mem_normalizer_iff.1 (hBn hb') (t⁻¹ * z * t)
            rw [mem_gLBConj, mem_gLBConj] at h2
            have e1 : t * (t⁻¹ * z * t) * t⁻¹ = z := by group
            have e2 : t * (b' * (t⁻¹ * z * t) * b'⁻¹) * t⁻¹ = t * b' * t⁻¹ * z * (t * b' * t⁻¹)⁻¹ := by
              group
            rw [e1, e2] at h2
            exact h2
          have e3 : ⁅t, b'⁆ = t * b' * t⁻¹ * b'⁻¹ := by
            rw [commutatorElement_def]
          rw [e3]
          exact Subgroup.mul_mem _ h1 (inv_mem (hBL hb'))
        exact ⟨barX 3 C ⁅T₀, B⁆, l94t_isPGroup_barX hT'X hT'2,
          l94t_barX_ne_bot hT'X hT'2 hne hodd, l94t_barX_le_normalizer (p := 3) hT'X hT'B,
          l94t_barX_le_normalizer (p := 3) hLC hTN⟩
    · left
      have heven : 2 ∣ Nat.card (GLAPPrimeCoreOf 3 C) :=
        even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
      intro P hP
      have := card_le_of_quot_even (G := G) (C := C) heven hP
      rw [hBbcard, hBcard]
      exact this
  exact noTriality_core hFK hKc hBbel hBbK hout hcase

end Wrapper

end CFSG.LocalAnalysis.GLTheoremA.D4T
