module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Fusion1
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3SigFacts

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Fin76b
  CFSG.EvenSporadicStandard.M23Std CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
  {T₁ : Subgroup (centralizer ({z} : Set G))} {F : Subgroup (L ⧸ center L)}
  {tb : L ⧸ center L} {Q : Sylow 2 G} {x : G} {L1 : Subgroup G}

set_option quotPrecheck false in
local notation "Hc" => centralizer ({z} : Set G)

theorem OutData.mem_normalizer_lift_of_mem_T (D : OutData L z t T₁ F tb) {g : G}
    (hg : g ∈ (T₁.map (Subgroup.subtype Hc) : Subgroup G)) :
    g ∈ normalizer (liftSub F : Set G) := by
  have hgH : g ∈ Hc := D.cfg.T_le hg
  have hgT : (⟨g, hgH⟩ : ↥Hc) ∈ T₁ := (D.mem_T_iff hgH).1 hg
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    exact D.T₁_normalizes_lift hgT ha
  · intro ha
    have := D.T₁_normalizes_lift (T₁.inv_mem hgT) ha
    have e1 : (↑(⟨g, hgH⟩⁻¹ : ↥Hc) : G) * (g * a * g⁻¹) * (↑(⟨g, hgH⟩⁻¹ : ↥Hc) : G)⁻¹ = a := by
      show g⁻¹ * (g * a * g⁻¹) * (g⁻¹)⁻¹ = a
      group
    rwa [e1] at this

theorem OuterSituation.T_le_normalizer (hS : OuterSituation G L z t T₁ F tb Q x L1) :
    (T₁.map (Subgroup.subtype Hc) : Subgroup G) ≤ normalizer (L1 : Set G) := by
  obtain ⟨N, Sup⟩ := OutSetup.of_kStructure hS.one hS.transitive hS.K
  obtain ⟨A, hLA, hAH, hzA, hAz, hidx⟩ := hS.complement
  have D := hS.data
  have hXE := Sup.inf_centralizer_eq hAH hAz
  have hzc : ∀ g ∈ A, z * g = g * z := fun g hg =>
    (mem_centralizer_singleton_iff.1 (hAH hg)).symm
  have hzcA : zpowers z ≤ centralizer (A : Set G) :=
    Subgroup.zpowers_le.2 (mem_centralizer_iff.2 fun a ha => (hzc a ha).symm)
  have hzNF : z ∈ normalizer (liftSub F : Set G) :=
    Subgroup.mem_normalizer_iff.2 (normalizes_of_centralizes fun f hf =>
      Sup.one.z_comm f (Sup.one.F_le hf))
  intro e he
  have heH : e ∈ Hc := D.cfg.T_le he
  have heN : e ∈ normalizer (liftSub F : Set G) := D.mem_normalizer_lift_of_mem_T he
  have heA : e ∈ A ⊔ zpowers z := by rw [hAz]; exact heH
  obtain ⟨a, haA, w, hw, hae⟩ := exists_mul_of_mem_sup_of_le_centralizer hzcA heA
  have hwN : w ∈ normalizer (liftSub F : Set G) := Subgroup.zpowers_le.2 hzNF hw
  have haN : a ∈ normalizer (liftSub F : Set G) := by
    rw [show a = e * w⁻¹ from eq_mul_inv_of_mul_eq hae.symm]
    exact Subgroup.mul_mem _ heN (Subgroup.inv_mem _ hwN)
  have ha' : a ∈ normalizer (liftSub F : Set G) ⊓ A := Subgroup.mem_inf.2 ⟨haN, haA⟩
  have : e ∈ zpowers z ⊔ (normalizer (liftSub F : Set G) ⊓ A) := by
    have h' : a * w ∈ (normalizer (liftSub F : Set G) ⊓ A) ⊔ zpowers z :=
      Subgroup.mul_mem_sup ha' hw
    rwa [sup_comm, ← hae] at h'
  rw [← hXE] at this
  exact (Subgroup.mem_inf.1 this).1


theorem factorization_two_192 : (Nat.factorization 192) 2 = 6 := by
  have h1 : 6 ≤ (192 : ℕ).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by norm_num)).1 (by norm_num)
  have h2 : ¬ 7 ≤ (192 : ℕ).factorization 2 := fun h =>
    absurd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by norm_num)).2 h)
      (by norm_num)
  omega

theorem OuterSituation.exists_sigma_data
    (hEng : AutSylowEngine6 (Carrier .M22))
    (hCens : AutSylowWith (fun Y _ F => AutCensus Y F) (Carrier .M22))
    (hFacts : AutSylowWith3
      (fun Y _ S F => ∃ J : Subgroup (MulAut Y), E32FactsX Y S F J) (Carrier .M22))
    (hS : OuterSituation G L z t T₁ F tb Q x L1) :
    ∃ (A : Subgroup G) (a : G), L ≤ A ∧ A ≤ centralizer ({z} : Set G) ∧ z ∉ A ∧
      A ⊔ zpowers z = centralizer ({z} : Set G) ∧ (L.subgroupOf A).index = 2 ∧
      NormQuot (Equiv.Perm (Fin 6)) (normalizer (liftSub F : Set G) ⊓ A) (liftSub F) ∧
      a ∈ A ∧ a ∉ L ∧ a * a = 1 ∧ a ∈ (T₁.map (Subgroup.subtype Hc) : Subgroup G) ∧
      a ∈ normalizer (liftSub F : Set G) ∧ a ∈ normalizer (L1 : Set G) ∧
      (∀ y, (y = a ∨ y = z * a) → Nat.card ↥(centralizer ({y} : Set G) ⊓ L1) ≤ 16 ∧
        (IsConj z y → ∃ k ∈ normalizer (L1 : Set G), ∃ l ∈ L1, k * z * k⁻¹ = y * l)) := by
  classical
  obtain ⟨N, Sup⟩ := OutSetup.of_kStructure hS.one hS.transitive hS.K
  have D := hS.data
  obtain ⟨A, hLA, hAH, hzA, hAz, hidx⟩ := hS.complement
  have hq : IsSporadic (L ⧸ center L) .M22 :=
    isSporadic_quotient_of_center_eq_bot D.Zbot hS.sporadic
  have hcZ : center (L ⧸ center L) = ⊥ := center_eq_bot_of_isSporadic hq
  have hout := innAut_index_dvd_two hq
  obtain ⟨e⟩ := hq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2' : orderOf z = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact D.cfg.z_sq) D.cfg.z_ne
  have hθ := thetaH_surjective_of_rel hS.std hS.cyclic D.cfg.z_cent hz2' D.cfg.cent_le hout hS.rel
  have hE6 := D.engine6 hcZ (hEng.of_mulEquiv e.symm)
  have hC' : AutCensus (L ⧸ center L) F :=
    D.property (P := fun Y _ F => AutCensus Y F) hcZ
      (AutSylowWith.of_mulEquiv AutCensus.isoInv e.symm hCens)
  have hquot := D.normQuot_A hcZ hθ hLA hAH hzA hAz hE6.s6
  have hcens := D.dCensus hcZ hθ hLA hAH hzA hAz hC'
  have hF3 : AutSylowWith3
      (fun Y _ S F => ∃ J : Subgroup (MulAut Y), E32FactsX Y S F J) (L ⧸ center L) :=
    AutSylowWith3.of_mulEquiv isoInv3_e32x e.symm hFacts
  obtain ⟨J, hJ⟩ := D.property3 hcZ hF3
  obtain ⟨E, b, hET, hEc, hEs, hEcard, hzE, hT1, hT2, -, -, -, -, -, hsurj⟩ :=
    D.exists_E rfl hS.z_not_sq D.W.e16.card hJ.toE32Facts
  obtain ⟨xJ, hxJ, hxin, hxfix⟩ := hJ.exists_x
  have hz2 : z * z = 1 := Sup.one.z_mul_self
  have hzc : ∀ g ∈ A, z * g = g * z := fun g hg =>
    (mem_centralizer_singleton_iff.1 (hAH hg)).symm
  have hzcA : zpowers z ≤ centralizer (A : Set G) :=
    Subgroup.zpowers_le.2 (mem_centralizer_iff.2 fun a ha => (hzc a ha).symm)
  have hXE := Sup.inf_centralizer_eq hAH hAz
  have hzH : z ∈ Hc := mem_centralizer_singleton_iff.2 rfl
  obtain ⟨e0, he0H, he0E, he0θ⟩ := hsurj xJ hxJ
  have he0A : e0 ∈ A ⊔ zpowers z := by rw [hAz]; exact he0H
  obtain ⟨a, haA, w, hw, hae⟩ := exists_mul_of_mem_sup_of_le_centralizer hzcA he0A
  have haeq : a = e0 * w⁻¹ := eq_mul_inv_of_mul_eq hae.symm
  have hwE : w ∈ E := Subgroup.zpowers_le.2 hzE hw
  have haE : a ∈ E := by rw [haeq]; exact E.mul_mem he0E (E.inv_mem hwE)
  have haH : a ∈ Hc := hAH haA
  have hwH : w ∈ Hc := Subgroup.zpowers_le.2 hzH hw
  have haθ : thetaH D.cfg.cent_le ⟨a, haH⟩ = xJ := by
    have h1 : (⟨a, haH⟩ : ↥Hc) = ⟨e0, he0H⟩ * (⟨w, hwH⟩ : ↥Hc)⁻¹ := Subtype.ext haeq
    rw [h1, map_mul, map_inv, (D.ker ⟨w, hwH⟩).2 hw, inv_one, mul_one, he0θ]
  have haT : a ∈ (T₁.map (Subgroup.subtype Hc) : Subgroup G) := hET haE
  have haN : a ∈ normalizer (liftSub F : Set G) := D.mem_normalizer_lift_of_mem_T haT
  have haD : a ∈ normalizer (liftSub F : Set G) ⊓ A := Subgroup.mem_inf.2 ⟨haN, haA⟩
  have haL : a ∉ L := fun h => by
    have := (D.theta_mem_innerImage_top_iff hLA hzA ⟨a, haH⟩ haA).2 h
    rw [haθ] at this
    exact hxin this
  have ha2 : a * a = 1 := hEs a haE
  have hfix4 : Nat.card {y : G // y ∈ liftSub F ∧ a * y = y * a} = 4 := by
    rw [D.card_fixed_eq a haH, haθ]
    exact hxfix
  have haX : a ∈ normalizer (L1 : Set G) := by
    have : a ∈ zpowers z ⊔ (normalizer (liftSub F : Set G) ⊓ A) := Subgroup.mem_sup_right haD
    rw [← hXE] at this
    exact (Subgroup.mem_inf.1 this).1
  obtain ⟨-, -, -, -, -, -, -, hF1, hb, -, hcov⟩ := hcens
  have hμ2 : (⟨a, haD⟩ : ↥(normalizer (liftSub F : Set G) ⊓ A)) * ⟨a, haD⟩ = 1 :=
    Subtype.ext (by simpa using ha2)
  have hμ1 : (⟨a, haD⟩ : ↥(normalizer (liftSub F : Set G) ⊓ A)) ≠ 1 := fun h =>
    haL (by rw [show a = 1 from congrArg Subtype.val h]; exact L.one_mem)
  have hcl : Nat.card (centralizer ({(⟨a, haD⟩ : ↥(normalizer (liftSub F : Set G) ⊓ A))} :
      Set ↥(normalizer (liftSub F : Set G) ⊓ A))) = 192 := by
    rcases hcov _ hμ2 hμ1 with h | h | h | h | h
    · exact absurd (liftSub_le F ((hF1 _).1 h).1) haL
    · have h8 : Nat.card {y : G // y ∈ liftSub F ∧ a * y = y * a} = 8 := h.2.2.2
      omega
    · have h8 : Nat.card {y : G // y ∈ liftSub F ∧ a * y = y * a} = 8 := h.2.2.2
      omega
    · exact h.2.2.1
    · exact absurd (hb _ h).1 haL
  have hCDcard : Nat.card ↥(centralizer ({a} : Set G) ⊓ (normalizer (liftSub F : Set G) ⊓ A)) =
      192 := by
    have hsub : (centralizer ({a} : Set G) ⊓ (normalizer (liftSub F : Set G) ⊓ A)).subgroupOf
        (normalizer (liftSub F : Set G) ⊓ A) =
        centralizer ({(⟨a, haD⟩ : ↥(normalizer (liftSub F : Set G) ⊓ A))} :
          Set ↥(normalizer (liftSub F : Set G) ⊓ A)) := by
      ext w'
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_singleton_iff,
        mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨h, -⟩
        exact Subtype.ext h
      · intro h
        exact ⟨congrArg Subtype.val h, w'.2⟩
    rw [← hcl, ← hsub]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  set CD : Subgroup G := centralizer ({a} : Set G) ⊓ (normalizer (liftSub F : Set G) ⊓ A)
    with hCD
  have hEACD : E ⊓ A ≤ CD := by
    intro g hg
    obtain ⟨hgE, hgA⟩ := Subgroup.mem_inf.1 hg
    exact Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 (hEc g hgE a haE),
      Subgroup.mem_inf.2 ⟨D.mem_normalizer_lift_of_mem_T (hET hgE), hgA⟩⟩
  have hEp : IsPGroup 2 ↥E := IsPGroup.of_card (n := 6) (by rw [hEcard]; norm_num)
  have hEA2 : IsPGroup 2 ((E ⊓ A).subgroupOf CD) := (hEp.to_inf_left).comap_subtype
  obtain ⟨Sy, hSy⟩ := hEA2.exists_le_sylow
  set Cb : Subgroup G := (Sy : Subgroup ↥CD).map CD.subtype with hCbdef
  have hCbsyl : IsSylowOf 2 Cb CD := ⟨Sy, rfl⟩
  have hCb64 : Nat.card Cb = 64 := by
    rw [hCbsyl.card_eq, hCDcard, factorization_two_192]
    norm_num
  have hCbCD : Cb ≤ CD := hCbsyl.le
  have hCbA : ∀ g ∈ Cb, g ∈ A := fun g hg =>
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (hCbCD hg)).2).2
  have hCba : ∀ g ∈ Cb, g * a = a * g := fun g hg =>
    mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hCbCD hg)).1
  have hzCb : z ∉ Cb := fun h => hzA (hCbA z h)
  have hzNCb : ∀ g, g ∈ Cb ↔ z * g * z⁻¹ ∈ Cb :=
    normalizes_of_centralizes fun g hg => hzc g (hCbA g hg)
  have hQcard : Nat.card ↥(Cb ⊔ zpowers z) = 128 := by
    rw [card_sup_zpowers_invol hz2 hzNCb hzCb, hCb64]
  have hQp : IsPGroup 2 ↥(Cb ⊔ zpowers z) := IsPGroup.of_card (n := 7) (by rw [hQcard]; norm_num)
  have hQz : Cb ⊔ zpowers z ≤ Hc :=
    sup_le (fun g hg => hAH (hCbA g hg)) (Subgroup.zpowers_le.2 hzH)
  have hCbX : ∀ g ∈ Cb, g ∈ normalizer (L1 : Set G) := by
    intro g hg
    have : g ∈ zpowers z ⊔ (normalizer (liftSub F : Set G) ⊓ A) :=
      Subgroup.mem_sup_right (Subgroup.mem_inf.1 (hCbCD hg)).2
    rw [← hXE] at this
    exact (Subgroup.mem_inf.1 this).1
  have hQN : Cb ⊔ zpowers z ≤ normalizer (L1 : Set G) :=
    sup_le hCbX (Subgroup.zpowers_le.2 Sup.zX.2)
  have hEQ : E ≤ Cb ⊔ zpowers z := by
    intro e' he'
    have he'H : e' ∈ Hc := D.cfg.T_le (hET he')
    have he'A : e' ∈ A ⊔ zpowers z := by rw [hAz]; exact he'H
    obtain ⟨a', ha'A, w', hw', hae'⟩ := exists_mul_of_mem_sup_of_le_centralizer hzcA he'A
    have hw'E : w' ∈ E := Subgroup.zpowers_le.2 hzE hw'
    have ha'E : a' ∈ E := by
      rw [show a' = e' * w'⁻¹ from eq_mul_inv_of_mul_eq hae'.symm]
      exact E.mul_mem he' (E.inv_mem hw'E)
    have ha'CD : a' ∈ CD := hEACD (Subgroup.mem_inf.2 ⟨ha'E, ha'A⟩)
    have ha'Cb : a' ∈ Cb := ⟨⟨a', ha'CD⟩, hSy (Subgroup.mem_subgroupOf.2
      (Subgroup.mem_inf.2 ⟨ha'E, ha'A⟩)), rfl⟩
    rw [hae']
    exact Subgroup.mul_mem_sup ha'Cb hw'
  have hKp : IsPGroup 2 ↥(L1 ⊔ zpowers z) := by
    have := hS.K.K_pgroup
    rwa [hS.K.K_eq] at this
  have hKs : ¬ 2 ∣ (L1 ⊔ zpowers z).relIndex (centralizer ((liftSub F : Subgroup G) : Set G)) := by
    have := hS.K.K_sylow
    rwa [hS.K.K_eq] at this
  have hzF : ∀ f ∈ liftSub F, z * f = f * z := fun f hf =>
    Sup.one.z_comm f (Sup.one.F_le hf)
  have hCG := hS.card_centralizer_z
  have hzN' : ∀ g, g ∈ L1 ↔ z * g * z ∈ L1 := fun g => by
    have := Sup.z_norm g
    rwa [inv_eq_of_mul_eq_one_right hz2] at this
  refine ⟨A, a, hLA, hAH, hzA, hAz, hidx, hquot, haA, haL, ha2, haT, haN, haX, ?_⟩
  intro y hy
  have hy2 : y * y = 1 := by
    rcases hy with hy | hy <;> rw [hy]
    · exact ha2
    · calc z * a * (z * a) = z * (a * z) * a := by group
        _ = z * (z * a) * a := by rw [← hzc a haA]
        _ = (z * z) * (a * a) := by group
        _ = 1 := by rw [hz2, ha2, one_mul]
  have hyz : y * z = z * y := by
    rcases hy with hy | hy <;> rw [hy]
    · exact (hzc a haA).symm
    · calc z * a * z = z * (a * z) := by group
        _ = z * (z * a) := by rw [← hzc a haA]
  have hyX : y ∈ normalizer (L1 : Set G) := by
    rcases hy with hy | hy <;> rw [hy]
    · exact haX
    · exact Subgroup.mul_mem _ Sup.zX.2 haX
  have hyE : y ∈ E := by
    rcases hy with hy | hy <;> rw [hy]
    · exact haE
    · exact E.mul_mem hzE haE
  have hQy : Cb ⊔ zpowers z ≤ centralizer ({y} : Set G) := by
    refine sup_le (fun g hg => ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [mem_centralizer_singleton_iff]
      rcases hy with hy | hy <;> rw [hy]
      · exact hCba g hg
      · have hgz : g * z = z * g := (hzc g (hCbA g hg)).symm
        calc g * (z * a) = (g * z) * a := by group
          _ = z * g * a := by rw [hgz]
          _ = z * (g * a) := by group
          _ = z * (a * g) := by rw [hCba g hg]
          _ = (z * a) * g := by group
    · rw [mem_centralizer_singleton_iff]
      exact hyz.symm
  have hW : Nat.card ↥(centralizer ({y} : Set G) ⊓ liftSub F) = 4 := by
    rw [← hfix4]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun w' => ?_)
    rw [Subgroup.mem_inf, mem_centralizer_singleton_iff]
    rcases hy with hy | hy <;> rw [hy]
    · exact ⟨fun h => ⟨h.2, h.1.symm⟩, fun h => ⟨h.2.symm, h.1⟩⟩
    · constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h2, ?_⟩
        have h3 : w' * z = z * w' := (hzF w' h2).symm
        have h4 : z * (w' * a) = z * (a * w') := by
          calc z * (w' * a) = z * w' * a := by group
            _ = w' * z * a := by rw [← h3]
            _ = w' * (z * a) := by group
            _ = (z * a) * w' := h1
            _ = z * (a * w') := by group
        exact (mul_left_cancel h4).symm
      · rintro ⟨h2, h1⟩
        refine ⟨?_, h2⟩
        have h3 : w' * z = z * w' := (hzF w' h2).symm
        calc w' * (z * a) = (w' * z) * a := by group
          _ = z * w' * a := by rw [h3]
          _ = z * (w' * a) := by group
          _ = z * (a * w') := by rw [← h1]
          _ = (z * a) * w' := by group
  have hU16 := Sup.sixteen_le_card_centralizer_L1 hyX hy2
  refine ⟨card_centralizer_le_sixteen Sup.L1_comm Sup.L1_sq hz2 hzN' hyz Sup.L1_cz hW, ?_⟩
  intro hyc
  exact exists_normalizer_conj_of_fusion (T := T₁.map (Subgroup.subtype Hc)) (E := E)
    (Q := Cb ⊔ zpowers z) (F := liftSub F) (L1 := L1) (z := z) (y := y)
    Sup.L1_comm Sup.L1_sq Sup.L1_card hz2 (Subgroup.mem_normalizer_iff.1 Sup.zX.2)
    hS.K.z_not_mem Sup.F_le Sup.one.F_card hzF Sup.L1_cz hKp hKs hS.K.not_conj Sup.one.fused
    hy2 hyz (Subgroup.mem_normalizer_iff.1 hyX) hyc hCG hU16 hW D.cfg.T_le D.cfg.T_pgroup
    D.T_relIndex_odd hEc hEs hEcard hzE hyE hT1 hT2 hQN hQy hQz hEQ hQp (by rw [hQcard])

end CFSG.EvenSporadicStandard.M22Std
