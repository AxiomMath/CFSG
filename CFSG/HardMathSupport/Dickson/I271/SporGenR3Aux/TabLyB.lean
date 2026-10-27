module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ConstrainedGen
public import CFSG.Sporadic.Recognition.LyonsLocalCentralizerE
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.Sporadic.HNSchreier.Algebra
public import CFSG.Sporadic.Suz.Simple
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Yardstones.Md0ec50421ce4
  CFSG.Sporadic.Recognition.LyonsSims CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open Subgroup Equiv

section ThreeB

variable {G : Type} [Group G] [Finite G] {t : G} {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

theorem tabLy_QE_le (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    QE (x₁ : G) (x₂ : G) ≤ centralizer ({(x₁ : G) * (x₂ : G)} : Set G) := by
  intro g hg
  rw [mem_QE] at hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g * ((x₁ : G) * (x₂ : G)) = (g * (x₁ : G)) * (x₂ : G) := by group
    _ = ((x₁ : G) * g) * (x₂ : G) := by rw [hg.1]
    _ = (x₁ : G) * (g * (x₂ : G)) := by group
    _ = (x₁ : G) * ((x₂ : G) * g) := by rw [hg.2]
    _ = (x₁ : G) * (x₂ : G) * g := by group

theorem tabLy_centralizer_le_QE {R : Subgroup G} (h₁ : (x₁ : G) ∈ R) (h₂ : (x₂ : G) ∈ R) :
    centralizer (R : Set G) ≤ QE (x₁ : G) (x₂ : G) := by
  intro g hg
  rw [mem_QE]
  exact ⟨Subgroup.mem_centralizer_iff.1 hg _ h₁, Subgroup.mem_centralizer_iff.1 hg _ h₂⟩

theorem tabLy_five_aux {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') {y₁ y₂ : K'}
    (c₁ : Nat.card ↥(centralizer ({y₁} : Set K')) = 750)
    (c₂ : Nat.card ↥(centralizer ({y₂} : Set K')) = 25)
    (hall : ∀ y : K', orderOf y = 5 → IsConj y y₁ ∨ IsConj y y₂) {u : K} (hu : orderOf u = 5) :
    ¬ 243 ∣ Nat.card ↥(centralizer ({u} : Set K)) := by
  have heu : orderOf (e u) = 5 := by rw [MulEquiv.orderOf_eq]; exact hu
  rw [← card_centralizer_mulEquiv e u]
  rcases hall _ heu with h | h
  · rw [CFSG.Sporadic.Recognition.LyonsSims.card_centralizer_eq_of_isConj h, c₁]
    norm_num
  · rw [CFSG.Sporadic.Recognition.LyonsSims.card_centralizer_eq_of_isConj h, c₂]
    norm_num

theorem tabLy_orderOf_x₁x₂ (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    orderOf ((x₁ : G) * (x₂ : G)) = 3 := by
  have h12 : Commute (x₁ : G) (x₂ : G) := (D.comm₂₁ S).symm
  have h3 : ((x₁ : G) * (x₂ : G)) ^ 3 = 1 := by
    rw [h12.mul_pow]
    have e1 : (x₁ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val S.pow₁
    have e2 : (x₂ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val S.pow₂
    rw [e1, e2, one_mul]
  have h1 : (x₁ : G) * (x₂ : G) ≠ 1 := by
    intro h
    have hH : x₁ * x₂ = 1 := Subtype.ext (by simpa using h)
    have := congrArg ρ hH
    rw [map_mul, S.rho₁, S.rho₂, map_one] at this
    revert this
    decide
  exact orderOf_eq_prime h3 h1

theorem tabLy_card_imageR (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) {R : Subgroup G}
    (hR : ThreeCoreE (x₁ : G) (x₂ : G) R) :
    Nat.card ↥((R.subgroupOf (centralizer ({(x₁ : G)} : Set G))).map (projQ (x₁ : G))) = 243 := by
  have hRC : R ≤ centralizer ({(x₁ : G)} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.2 ((mem_QE.1 (hR.le hr)).1).symm
  set R' := R.subgroupOf (centralizer ({(x₁ : G)} : Set G)) with hR'
  let φ : ↥R' →* CentQuot (x₁ : G) := (projQ (x₁ : G)).comp R'.subtype
  have hrange : φ.range = R'.map (projQ (x₁ : G)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hx₁R' : (⟨(x₁ : G), self_mem_centralizer_singleton _⟩ :
      ↥(centralizer ({(x₁ : G)} : Set G))) ∈ R' := Subgroup.mem_subgroupOf.2 hR.left_mem
  have hker : φ.ker.map R'.subtype = zpowers (⟨(x₁ : G), self_mem_centralizer_singleton _⟩ :
      ↥(centralizer ({(x₁ : G)} : Set G))) := by
    ext y
    constructor
    · rintro ⟨r, hr, rfl⟩
      have : (r : ↥(centralizer ({(x₁ : G)} : Set G))) ∈ (projQ (x₁ : G)).ker := hr
      rwa [ker_projQ] at this
    · intro hy
      have hyR : y ∈ R' := (Subgroup.zpowers_le.2 hx₁R') hy
      refine ⟨⟨y, hyR⟩, ?_, rfl⟩
      show projQ (x₁ : G) y = 1
      have : y ∈ (projQ (x₁ : G)).ker := by rw [ker_projQ]; exact hy
      exact this
  have hkc : Nat.card ↥φ.ker = 3 := by
    rw [← Subgroup.card_map_of_injective R'.subtype_injective, hker, Nat.card_zpowers,
      Subgroup.orderOf_mk, LyData.orderOf_x₁ S]
  have hRc : Nat.card ↥R' = 729 := by
    rw [hR', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv, hR.card]
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hkc, hRc, hrange] at h
  omega


theorem tabLy_relindex_le_two (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hord : Nat.card ↥(centralizer ({(x₁ : G) * (x₂ : G)} : Set G)) ≤ 174960) :
    (QE (x₁ : G) (x₂ : G)).relIndex (centralizer ({(x₁ : G) * (x₂ : G)} : Set G)) ≤ 2 := by
  have hle := tabLy_QE_le D S
  have h1 := Subgroup.card_mul_index ((QE (x₁ : G) (x₂ : G)).subgroupOf
    (centralizer ({(x₁ : G) * (x₂ : G)} : Set G)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, D.card_QE S] at h1
  have h2 : (QE (x₁ : G) (x₂ : G)).relIndex (centralizer ({(x₁ : G) * (x₂ : G)} : Set G)) =
      ((QE (x₁ : G) (x₂ : G)).subgroupOf (centralizer ({(x₁ : G) * (x₂ : G)} : Set G))).index :=
    rfl
  rw [h2]
  omega

theorem tabLy_QE_normal (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hord : Nat.card ↥(centralizer ({(x₁ : G) * (x₂ : G)} : Set G)) ≤ 174960) :
    ∀ c ∈ centralizer ({(x₁ : G) * (x₂ : G)} : Set G), ∀ q ∈ QE (x₁ : G) (x₂ : G),
      c * q * c⁻¹ ∈ QE (x₁ : G) (x₂ : G) := by
  intro c hc q hq
  have hle := tabLy_QE_le D S
  have hpos : (QE (x₁ : G) (x₂ : G)).relIndex (centralizer ({(x₁ : G) * (x₂ : G)} : Set G)) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have h2 := tabLy_relindex_le_two D S hord
  rcases (show (QE (x₁ : G) (x₂ : G)).relIndex (centralizer ({(x₁ : G) * (x₂ : G)} : Set G)) = 1 ∨
      (QE (x₁ : G) (x₂ : G)).relIndex (centralizer ({(x₁ : G) * (x₂ : G)} : Set G)) = 2 by
    omega) with h | h
  · have hcQ : c ∈ QE (x₁ : G) (x₂ : G) := Subgroup.relIndex_eq_one.1 h hc
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcQ hq) (Subgroup.inv_mem _ hcQ)
  · have hn : ((QE (x₁ : G) (x₂ : G)).subgroupOf
        (centralizer ({(x₁ : G) * (x₂ : G)} : Set G))).Normal :=
      Subgroup.normal_of_index_eq_two h
    have := hn.conj_mem ⟨q, hle hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨c, hc⟩
    exact Subgroup.mem_subgroupOf.1 this

theorem tabLy_le_QE_of_isPGroup (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hord : Nat.card ↥(centralizer ({(x₁ : G) * (x₂ : G)} : Set G)) ≤ 174960) {J : Subgroup G}
    (hJ : J ≤ centralizer ({(x₁ : G) * (x₂ : G)} : Set G)) (hJ3 : IsPGroup 3 J) :
    J ≤ QE (x₁ : G) (x₂ : G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 := tabLy_relindex_le_two D S hord
  have hne : (QE (x₁ : G) (x₂ : G)).relIndex (centralizer ({(x₁ : G) * (x₂ : G)} : Set G)) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hJle : (QE (x₁ : G) (x₂ : G)).relIndex J ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right hJ hne).trans h2
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hJ3
  have hdvd : (QE (x₁ : G) (x₂ : G)).relIndex J ∣ 3 ^ n := hn ▸ Subgroup.relIndex_dvd_card _ _
  have h1 : (QE (x₁ : G) (x₂ : G)).relIndex J = 1 := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    rw [hk] at hJle ⊢
    rcases k with _ | k
    · rfl
    · exfalso
      have : 3 ≤ 3 ^ (k + 1) := by
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  exact Subgroup.relIndex_eq_one.1 h1

theorem tabLy_R_normal (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hord : Nat.card ↥(centralizer ({(x₁ : G) * (x₂ : G)} : Set G)) ≤ 174960) {R : Subgroup G}
    (hR : ThreeCoreE (x₁ : G) (x₂ : G) R) :
    ∀ c ∈ centralizer ({(x₁ : G) * (x₂ : G)} : Set G), ∀ r ∈ R, c * r * c⁻¹ ∈ R := by
  intro c hc r hr
  have hQn := tabLy_QE_normal D S hord
  let J : Subgroup G := R.map (MulAut.conj c).toMonoidHom
  have hJQ : J ≤ QE (x₁ : G) (x₂ : G) := by
    rintro _ ⟨r', hr', rfl⟩
    exact hQn c hc r' (hR.le hr')
  have hJn : ∀ g ∈ QE (x₁ : G) (x₂ : G), ∀ j ∈ J, g * j * g⁻¹ ∈ J := by
    rintro g hg _ ⟨r', hr', rfl⟩
    have hc' : c⁻¹ ∈ centralizer ({(x₁ : G) * (x₂ : G)} : Set G) := Subgroup.inv_mem _ hc
    have hg' : c⁻¹ * g * c⁻¹⁻¹ ∈ QE (x₁ : G) (x₂ : G) := hQn _ hc' g hg
    refine ⟨(c⁻¹ * g * c⁻¹⁻¹) * r' * (c⁻¹ * g * c⁻¹⁻¹)⁻¹, hR.normal _ hg' r' hr', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hJ3 : IsPGroup 3 J := hR.isPGroup.map _
  have := hR.max J hJQ hJn hJ3 ⟨r, hr, rfl⟩
  simpa [J] using this

theorem tabLy_R_max (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hord : Nat.card ↥(centralizer ({(x₁ : G) * (x₂ : G)} : Set G)) ≤ 174960) {R : Subgroup G}
    (hR : ThreeCoreE (x₁ : G) (x₂ : G) R) :
    ∀ J : Subgroup G, J ≤ centralizer ({(x₁ : G) * (x₂ : G)} : Set G) →
      (∀ c ∈ centralizer ({(x₁ : G) * (x₂ : G)} : Set G), ∀ j ∈ J, c * j * c⁻¹ ∈ J) →
        IsPGroup 3 J → J ≤ R := by
  intro J hJC hJn hJ3
  have hJQ := tabLy_le_QE_of_isPGroup D S hord hJC hJ3
  exact hR.max J hJQ (fun g hg j hj => hJn g (tabLy_QE_le D S hg) j hj) hJ3


theorem tabLy_not_dvd_cent_five (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    {u : CentQuot (x₁ : G)} (hu : orderOf u = 5) :
    ¬ 243 ∣ Nat.card ↥(centralizer ({u} : Set (CentQuot (x₁ : G)))) := by
  obtain ⟨e⟩ := D.centQuot_mcl S.pow₁ S.rho₁
  obtain ⟨y₁, y₂, -, -, c₁, c₂, -, hall⟩ :=
    CFSG.Sporadic.Recognition.McLAS.mcl_two_classes_order_five_of_certificate
  exact @tabLy_five_aux (CentQuot (x₁ : G)) NativeSporadic.McL _ inferInstance e y₁ y₂ c₁ c₂ hall
    u hu

theorem tabLy_solvable_cent (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) {R : Subgroup G}
    (hR : ThreeCoreE (x₁ : G) (x₂ : G) R) :
    Group.IsSolvable ↥(centralizer ({(x₁ : G) * (x₂ : G)} : Set G) ⊓ centralizer (R : Set G)) := by
  set N := centralizer ({(x₁ : G) * (x₂ : G)} : Set G) ⊓ centralizer (R : Set G) with hN
  have hNQ : N ≤ QE (x₁ : G) (x₂ : G) :=
    inf_le_right.trans (tabLy_centralizer_le_QE hR.left_mem hR.right_mem)
  have hQC : QE (x₁ : G) (x₂ : G) ≤ centralizer ({(x₁ : G)} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 ((mem_QE.1 hg).1).symm
  have hdvdQ : Nat.card ↥N ∣ 2 ^ 3 * 3 ^ 7 * 5 := by
    have := Subgroup.card_dvd_of_le hNQ
    rw [D.card_QE S] at this
    simpa using this
  have h5 : ¬ 5 ∣ Nat.card ↥N := by
    intro h5
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 5 h5
    have hu5 : orderOf (u : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hu
    have huC : (u : G) ∈ centralizer ({(x₁ : G)} : Set G) := hQC (hNQ u.2)
    set ū := projQ (x₁ : G) ⟨(u : G), huC⟩ with hū
    have hū5 : orderOf ū = 5 := by
      have hpow : ū ^ 5 = 1 := by
        rw [hū, ← map_pow]
        have : (⟨(u : G), huC⟩ : ↥(centralizer ({(x₁ : G)} : Set G))) ^ 5 = 1 := by
          apply Subtype.ext
          rw [SubgroupClass.coe_pow, ← hu5]
          exact pow_orderOf_eq_one _
        rw [this, map_one]
      have hne : ū ≠ 1 := by
        intro h1
        have hk : (⟨(u : G), huC⟩ : ↥(centralizer ({(x₁ : G)} : Set G))) ∈
            (projQ (x₁ : G)).ker := h1
        rw [ker_projQ] at hk
        have hdvd := orderOf_dvd_of_mem_zpowers hk
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, LyData.orderOf_x₁ S, hu5] at hdvd
        norm_num at hdvd
      haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      exact orderOf_eq_prime hpow hne
    have hle : (R.subgroupOf (centralizer ({(x₁ : G)} : Set G))).map (projQ (x₁ : G)) ≤
        centralizer ({ū} : Set (CentQuot (x₁ : G))) := by
      rintro _ ⟨r, hr, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, hū, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 u.2).2
        _ (Subgroup.mem_subgroupOf.1 hr)
      simpa using this
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [tabLy_card_imageR D S hR] at hdvd
    exact tabLy_not_dvd_cent_five D S hū5 hdvd
  have hcop : Nat.Coprime (Nat.card ↥N) 5 :=
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5))
  have h2 : Nat.card ↥N ∣ 2 ^ 3 * 3 ^ 7 := hcop.dvd_of_dvd_mul_right hdvdQ
  exact isSolvable_of_card_dvd_two_three h2


theorem tabLy_threeB (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hord : Nat.card ↥(centralizer ({(x₁ : G) * (x₂ : G)} : Set G)) ≤ 174960)
    (hO : GLAPPrimeCoreOf 3 (centralizer ({(x₁ : G) * (x₂ : G)} : Set G)) = ⊥) :
    PConstrainedShape 3 (centralizer ({(x₁ : G) * (x₂ : G)} : Set G)) := by
  obtain ⟨R, hR⟩ := D.exists_threeCoreE S
  exact pConstrainedShape_of_centralizer_solvable Nat.prime_three (hR.le.trans (tabLy_QE_le D S))
    (tabLy_R_normal D S hord hR) hR.isPGroup (tabLy_R_max D S hord hR) hO
    (tabLy_solvable_cent D S hR)

end ThreeB

end CFSG.HardMathSupport.Dickson.I271
