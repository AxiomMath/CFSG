module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Weak
public import Certificates.Certificate43
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3 JData)
open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.Open (IsElemAbelian)

section Basic

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G}

omit [Finite G] in
theorem _root_.CFSG.ComponentClassification.RankTwoClassical.JData.mem_centralizer_of_commute
    {T J : Subgroup G} {p y : G} (hJ : JData A R T p J y) {a z : G} (ha : a ∈ A) (hz : z ∈ J)
    (hz1 : z ≠ 1) (haz : a * z = z * a) : a ∈ centralizer (J : Set G) := by
  obtain ⟨b, hb, hbz⟩ := hJ.trans p hJ.mem hJ.ne_one z hz hz1
  obtain ⟨hbA, hbJ⟩ := mem_inf.1 hb
  have hp : p = b⁻¹ * z * b := by rw [← hbz]; group
  have ha'A : b⁻¹ * a * b ∈ A := mul_mem (mul_mem (inv_mem hbA) ha) hbA
  have ha'p : b⁻¹ * a * b * p = p * (b⁻¹ * a * b) := by
    rw [hp]
    calc b⁻¹ * a * b * (b⁻¹ * z * b) = b⁻¹ * (a * z) * b := by group
      _ = b⁻¹ * (z * a) * b := by rw [haz]
      _ = b⁻¹ * z * b * (b⁻¹ * a * b) := by group
  have ha'N : b⁻¹ * a * b ∈ normalizer (J : Set G) :=
    hJ.le_normalizer (mem_inf.2 ⟨ha'A, mem_centralizer_singleton_iff.2 ha'p⟩)
  have ha'C := hJ.free _ (mem_inf.2 ⟨ha'A, ha'N⟩) p hJ.mem hJ.ne_one
    (by rw [ha'p, mul_inv_cancel_right])
  have e : a = b * (b⁻¹ * a * b) * b⁻¹ := by group
  rw [e]
  exact (mem_normalizer_iff.1 (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer _ hbJ) _).1 ha'C

end Basic

section Main

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}

theorem g2_short_inf_false'
    {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (h4 : Asc75Theorem4) (h32 : Lemma32) (h184 : G2Centr184)
    (h184s : G2Centr184s) (hc : Sec3 A R T g)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hTp : G2Pinned ψ T g2v) (hTv : ActsIn ψ T (rootSubgroup .G2 K g2v))
    (hnolong : ¬ ∃ (T' : Subgroup G) (g' : G), Sec3 A R T' g' ∧ G2Pinned ψ T' g2c ∧
      ActsIn ψ T' (rootSubgroup .G2 K g2c)) (hTA : T ⊓ A = ⊥) : False := by
  classical
  have h34 : Asc08Lemma34 := asc08Lemma34
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨hV, -, h2tr⟩ :=
    sec3V_case_two hf hK h4 h32 h184 h184s hc hOut hZA hψ hTv hnolong hTA
  obtain ⟨p, y, hJ⟩ := jData_of_actsIn hf hK h4 h32 hc hZA hψ hTv
  have hZ0 : twoLift ψ (rootSubgroup .G2 K g2v) = twoLift ψ (g2YGroup K 0 0) := by
    rw [g2YGroup_zero]
  rw [hZ0] at hV hJ
  rw [hV] at h2tr
  set B := twoLift ψ (g2ShortRadical K) with hBdef
  set W := twoLift ψ (g2BCGroup K) with hWdef
  set M := CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)) with hMdef
  set V := R ⊔ twoLift ψ (g2YGroup K 0 0) with hVdef
  have hWM : oTwoIn M = W := oTwoIn_perfectCore_eq h4 h32 h184s hK4 hc hZA hψ hTp hTv
  have hRB : R ⊔ B = V ⊔ oTwoIn M := by
    rw [hWM, hBdef, hWdef, hVdef, twoLift_radical_eq_sup hZA hψ 0 0, sup_assoc]
  have hVRB : V ≤ R ⊔ B := by rw [hRB]; exact le_sup_left
  obtain ⟨xT, hxT, hAxT⟩ := Lemma36.exists_conj_eq hc.sylowR hc.sylowT
  have hRneT : R ≠ T := by
    intro h
    apply hc.R_ne_bot
    have h1 := hc.inf_eq_bot
    rwa [← h, inf_idem] at h1
  have hTV : T ≤ V := hV ▸ (le_sup_right.trans (le_sec3V_of ⟨xT, hxT⟩))
  have hTR : ¬ T ≤ R := fun h => hc.T_ne_bot ((inf_eq_right.2 h).symm.trans hc.inf_eq_bot)
  have hcentR : ∀ a ∈ A, R.map (MulAut.conj a).toMonoidHom = R := by
    intro a ha
    refine map_conj_eq_self_of_centralizes (X := R) (fun r hr => ?_) le_rfl
    rw [mem_centralizer_iff.1 (hc.sylowR.le hr) a ha, mul_inv_cancel_right]
  have hCV : ∀ Q : Subgroup G, Q ≤ V → ¬ Q ≤ R →
      A ⊓ centralizer (Q : Set G) = A ⊓ centralizer (V : Set G) := by
    intro Q hQV hQR
    refine le_antisymm (fun a ha => ?_) (inf_le_inf_left _ (centralizer_le fun v hv => hQV hv))
    obtain ⟨haA, haQ⟩ := mem_inf.1 ha
    obtain ⟨t, htQ, htR⟩ := IsConcreteLE.not_le_iff_exists.1 hQR
    obtain ⟨r, hr, z, hz, rfl⟩ := exists_mul_of_mem_sup_twoLift hc _ (hQV htQ)
    have hz1 : z ≠ 1 := fun h => htR (by rw [h, mul_one]; exact hr)
    have har : a * r = r * a := mem_centralizer_iff.1 (hc.sylowR.le hr) a haA
    have hat : r * z * a = a * (r * z) := mem_centralizer_iff.1 haQ (r * z) htQ
    have haz : a * z = z * a := by
      have h1 : r * (z * a) = r * (a * z) := by
        calc r * (z * a) = r * z * a := (mul_assoc _ _ _).symm
          _ = a * (r * z) := hat
          _ = a * r * z := (mul_assoc _ _ _).symm
          _ = r * a * z := by rw [har]
          _ = r * (a * z) := mul_assoc _ _ _
      exact (mul_left_cancel h1).symm
    have haZ := hJ.mem_centralizer_of_commute haA hz hz1 haz
    refine mem_inf.2 ⟨haA, RankTwoClassical.mem_centralizer_sup ?_ haZ⟩
    exact mem_centralizer_iff.2 fun r' hr' => (mem_centralizer_iff.1 (hc.sylowR.le hr') a haA).symm
  set H : Subgroup G := normalizer ((R ⊔ B : Subgroup G) : Set G) ⊓ normalizer (W : Set G)
    with hHdef
  let Ω := {Q : Subgroup G // Q ≤ R ⊔ B ∧ ∃ x : G, Q = rightConjugate R x}
  have hmapΩ : ∀ (h : H) (Q : Ω), Q.1.map (MulAut.conj (h : G)).toMonoidHom ≤ R ⊔ B ∧
      ∃ x : G, Q.1.map (MulAut.conj (h : G)).toMonoidHom = rightConjugate R x := by
    rintro ⟨h, hhRB, -⟩ ⟨Q, hQ, x, rfl⟩
    refine ⟨?_, x * h⁻¹, by rw [map_conj_eq_rightConjugate, rightConjugate_mul]⟩
    have h1 := map_mono (f := (MulAut.conj h).toMonoidHom) hQ
    have h2 : (R ⊔ B).map (MulAut.conj h).toMonoidHom = R ⊔ B :=
      (mem_normalizer_iff_map_conj_eq).1 hhRB
    rwa [h2] at h1
  let _ : MulAction H Ω :=
    { smul := fun h Q => ⟨Q.1.map (MulAut.conj (h : G)).toMonoidHom, hmapΩ h Q⟩
      one_smul := fun Q => Subtype.ext (map_conj_one Q.1)
      mul_smul := fun h₁ h₂ Q => Subtype.ext (map_conj_mul Q.1 h₁ h₂).symm }
  have hsmul : ∀ (h : H) (Q : Ω),
      ((h • Q : Ω) : Subgroup G) = Q.1.map (MulAut.conj (h : G)).toMonoidHom := fun _ _ => rfl
  let R₀ : Ω := ⟨R, le_sup_left, 1, (rightConjugate_one R).symm⟩
  let T₀ : Ω := ⟨T, hTV.trans hVRB, xT, hxT⟩
  have hDH : unipStab A B W ≤ H := by
    intro d hd
    have hdR : d ∈ centralizer (R : Set G) := by
      rw [mem_centralizer_iff]
      intro r hr
      exact (mem_centralizer_iff.1 (hc.sylowR.le hr) d hd.1).symm
    refine mem_inf.2 ⟨RankTwoClassical.mem_normalizer_sup (centralizer_le_normalizer _ hdR)
      hd.2.1, centralizer_le_normalizer _ (mem_centralizer_iff.2 fun w hw => ?_)⟩
    exact (hd.2.2.2 w hw).symm
  have hnH : ∀ n y : G, n ∈ normalizer ((V : Subgroup G) : Set G) →
      rightConjugate R y ≤ V → rightConjugate R y ≠ R →
      rightConjugate R n = rightConjugate R y → rightConjugate T n = R → n ∈ H := by
    intro n y hnV hy hyne hRn hTn
    have hAgn : rightConjugate (rightConjugate A g) n = A := by
      rw [← hAxT, rightConjugate_mul]
      apply (rightConjugate_eq_self_iff A (xT * n)).2
      have h1 : xT * n ∈ normalizer (R : Set G) := by
        rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, ← hxT, hTn]
      have h2 := Lemma36.normalizer_le hc.hyp hc.sylowR 1 (by rwa [rightConjugate_one])
      rwa [rightConjugate_one] at h2
    have hM' : M = CFSG.Quasithin.perfectCore (rightConjugate A g ⊓ centralizer (R : Set G)) :=
      hc.perfectCore_eq h32 h4 h34 hOut
    have hyR : ¬ rightConjugate R y ≤ R := fun h =>
      hyne (eq_of_le_of_card_ge h (by rw [rightConjugate_card]))
    have hTV' : A ⊓ centralizer (T : Set G) = A ⊓ centralizer (V : Set G) := hCV T hTV hTR
    have hMn : rightConjugate M n = M := by
      calc rightConjugate M n = CFSG.Quasithin.perfectCore
            (rightConjugate (rightConjugate A g ⊓ centralizer (R : Set G)) n) := by
            rw [hM', RankTwoClassical.rightConjugate_perfectCore]
        _ = CFSG.Quasithin.perfectCore (A ⊓ centralizer (rightConjugate R y : Set G)) := by
            rw [RankTwoClassical.rightConjugate_inf, ← centralizer_rightConjugate, hAgn, hRn]
        _ = M := by rw [hCV _ hy hyR, ← hTV']
    have hnM : n ∈ normalizer (M : Set G) := (rightConjugate_eq_self_iff M n).1 hMn
    have hnW : n ∈ normalizer (W : Set G) := hWM ▸ mem_normalizer_oTwoIn hnM
    refine mem_inf.2 ⟨?_, hnW⟩
    rw [hRB]
    exact RankTwoClassical.mem_normalizer_sup hnV (mem_normalizer_oTwoIn hnM)
  have hreach : ∀ Q : Ω, ∃ h : H, h • R₀ = Q := by
    intro Q
    by_cases hQR : Q.1 = R
    · exact ⟨1, by rw [one_smul]; exact Subtype.ext hQR.symm⟩
    · obtain ⟨y, hy⟩ := Q.2.2
      have hyB : rightConjugate R y ≤ R ⊔ B := hy ▸ Q.2.1
      have hyne : rightConjugate R y ≠ R := hy ▸ hQR
      obtain ⟨α, γ, hαγ⟩ :=
        le_sup_lift_of_conj h4 h32 h184 h184s hK4 hc hOut hZA hψ hnolong hyB hyne
      rw [← hy] at hαγ
      obtain ⟨u, huD, hu⟩ := exists_lift_ru hZA hψ α γ
      have huA : u ∈ A := huD.1
      have hmapV : V.map (MulAut.conj u).toMonoidHom = R ⊔ twoLift ψ (g2YGroup K α γ) := by
        rw [hVdef, Subgroup.map_sup, hcentR u huA, hu]
      have hQ0y : Q.1.map (MulAut.conj u⁻¹).toMonoidHom = rightConjugate R (y * u) := by
        rw [hy, map_conj_eq_rightConjugate, inv_inv, rightConjugate_mul]
      have hQ0 : rightConjugate R (y * u) ≤ V := by
        rw [← hQ0y]
        have h1 := map_mono (f := (MulAut.conj u⁻¹).toMonoidHom) hαγ
        rwa [← hmapV, map_conj_mul, inv_mul_cancel, map_conj_one] at h1
      have hQ0ne : rightConjugate R (y * u) ≠ R := by
        intro h
        apply hQR
        have h1 : Q.1 = (Q.1.map (MulAut.conj u⁻¹).toMonoidHom).map
            (MulAut.conj u).toMonoidHom := by
          rw [map_conj_mul, mul_inv_cancel, map_conj_one]
        rw [h1, hQ0y, h, hcentR u huA]
      obtain ⟨n, hnV, hn1, hn2⟩ := h2tr 1 xT (y * u) 1
        (by rw [rightConjugate_one]; exact le_sup_left) (by rw [← hxT]; exact hTV) hQ0
        (by rw [rightConjugate_one]; exact le_sup_left)
        (by rw [rightConjugate_one, ← hxT]; exact hRneT) (by rw [rightConjugate_one]; exact hQ0ne)
      rw [rightConjugate_one] at hn1 hn2
      rw [← hxT] at hn2
      have hn : n ∈ H := hnH n (y * u) hnV hQ0 hQ0ne hn1 hn2
      refine ⟨⟨u, hDH huD⟩ * ⟨n, hn⟩⁻¹, Subtype.ext ?_⟩
      rw [hsmul]
      change R.map (MulAut.conj (u * n⁻¹)).toMonoidHom = Q.1
      rw [← map_conj_mul, map_conj_eq_rightConjugate R n⁻¹, inv_inv, hn1, ← hQ0y, map_conj_mul,
        mul_inv_cancel, map_conj_one]
  have hfib : ∀ Q : Subgroup G, Q ≤ R ⊔ B → (∃ x : G, Q = rightConjugate R x) →
      Q ⊔ W = R ⊔ W → Q = R := by
    rintro Q hQB ⟨y, rfl⟩ hQ
    by_contra hQR
    obtain ⟨α, γ, hαγ⟩ :=
      le_sup_lift_of_conj h4 h32 h184 h184s hK4 hc hOut hZA hψ hnolong hQB hQR
    have hle : rightConjugate R y ≤ R := by
      refine le_trans (le_inf ?_ hαγ) (sup_bc_inf_le hc hZA hψ α γ)
      rw [← hQ]
      exact le_sup_left
    exact hQR (eq_of_le_of_card_ge hle (by rw [rightConjugate_card]))
  obtain ⟨a₁, ha₁A, -, ha₁D, ha₁Y⟩ := exists_lift_r_mem hZA hψ (1 : K)
  have hTB : T ≤ R ⊔ B := hTV.trans hVRB
  have hneT : T.map (MulAut.conj a₁).toMonoidHom ≠ T := by
    intro h
    have hmap : V.map (MulAut.conj a₁).toMonoidHom = R ⊔ twoLift ψ (g2YGroup K 1 0) := by
      rw [hVdef, Subgroup.map_sup, hcentR a₁ ha₁A, ha₁Y, zero_add]
    have hT1 : T ≤ R ⊔ twoLift ψ (g2YGroup K 1 0) := by
      have h2 : T.map (MulAut.conj a₁).toMonoidHom ≤ V.map (MulAut.conj a₁).toMonoidHom :=
        map_mono hTV
      rwa [h, hmap] at h2
    exact hTR ((le_inf hTV hT1).trans (sup_lift_inf_le hc hZA hψ (Or.inl zero_ne_one)))
  have hT₁B : T.map (MulAut.conj a₁).toMonoidHom ≤ R ⊔ B := by
    have h1 := map_mono (f := (MulAut.conj a₁).toMonoidHom) hTB
    have h2 : (R ⊔ B).map (MulAut.conj a₁).toMonoidHom = R ⊔ B :=
      (mem_normalizer_iff_map_conj_eq).1 (mem_inf.1 (hDH ha₁D)).1
    rwa [h2] at h1
  have hmapT : T.map (MulAut.conj a₁).toMonoidHom ⊔ W = T ⊔ W := by
    refine le_antisymm (sup_le (map_conj_le_sup_of_mem_unipStab hc hZA hψ ha₁D hTB)
      le_sup_right) (sup_le ?_ le_sup_right)
    have h1 := map_conj_le_sup_of_mem_unipStab hc hZA hψ (inv_mem ha₁D) hT₁B
    rwa [map_conj_mul, inv_mul_cancel, map_conj_one] at h1
  obtain ⟨h, hh⟩ := hreach T₀
  have hhT : R.map (MulAut.conj (h : G)).toMonoidHom = T := congrArg Subtype.val hh
  have hhRB : (R ⊔ B).map (MulAut.conj (h : G)⁻¹).toMonoidHom = R ⊔ B :=
    (mem_normalizer_iff_map_conj_eq).1 (inv_mem (mem_inf.1 h.2).1)
  have hhW : W.map (MulAut.conj (h : G)⁻¹).toMonoidHom = W :=
    (mem_normalizer_iff_map_conj_eq).1 (inv_mem (mem_inf.1 h.2).2)
  set Q := (T.map (MulAut.conj a₁).toMonoidHom).map (MulAut.conj (h : G)⁻¹).toMonoidHom
    with hQdef
  have hQB : Q ≤ R ⊔ B := by
    have h1 := map_mono (f := (MulAut.conj (h : G)⁻¹).toMonoidHom) hT₁B
    rwa [hhRB] at h1
  have hQx : ∃ x : G, Q = rightConjugate R x := by
    refine ⟨xT * (a₁⁻¹ * (h : G)), ?_⟩
    rw [hQdef, hxT, map_conj_eq_rightConjugate, map_conj_eq_rightConjugate, rightConjugate_mul,
      rightConjugate_mul, inv_inv]
  have hQW : Q ⊔ W = R ⊔ W := by
    calc Q ⊔ W = (T.map (MulAut.conj a₁).toMonoidHom).map (MulAut.conj (h : G)⁻¹).toMonoidHom ⊔
          W.map (MulAut.conj (h : G)⁻¹).toMonoidHom := by rw [hhW]
      _ = (T.map (MulAut.conj a₁).toMonoidHom ⊔ W).map (MulAut.conj (h : G)⁻¹).toMonoidHom :=
          (Subgroup.map_sup _ _ _).symm
      _ = (T ⊔ W).map (MulAut.conj (h : G)⁻¹).toMonoidHom := by rw [hmapT]
      _ = R ⊔ W := by
          rw [Subgroup.map_sup, hhW, ← hhT, map_conj_mul, inv_mul_cancel, map_conj_one]
  have hQR := hfib Q hQB hQx hQW
  apply hneT
  calc T.map (MulAut.conj a₁).toMonoidHom = Q.map (MulAut.conj (h : G)).toMonoidHom := by
        rw [hQdef, map_conj_mul, mul_inv_cancel, map_conj_one]
    _ = R.map (MulAut.conj (h : G)).toMonoidHom := by rw [hQR]
    _ = T := hhT

theorem g2_long_of_short'
    {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (h4 : Asc75Theorem4) (h32 : Lemma32) (h184 : G2Centr184)
    (h184s : G2Centr184s) (hc : Sec3 A R T g)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hTp : G2Pinned ψ T g2v) (hTv : ActsIn ψ T (rootSubgroup .G2 K g2v)) :
    ∃ (T' : Subgroup G) (g' : G), Sec3 A R T' g' ∧ G2Pinned ψ T' g2c ∧
      ActsIn ψ T' (rootSubgroup .G2 K g2c) := by
  by_contra hno
  rcases inf_eq_bot_or_card_eq hf hK h4 h32 h184 h184s hc hOut hZA hψ hno with hTA | hRq
  · exact g2_short_inf_false' hf hK h4 h32 h184 h184s hc hOut hZA hψ hTp hTv hno hTA
  · exact hno (g2_long_of_short hf hK h4 h32 h184 h184s hc hOut hZA hψ hRq hTp hTv)

end Main

end CFSG.ComponentClassification.RankTwoExceptional
