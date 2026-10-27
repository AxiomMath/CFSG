module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDichotomy

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G]

structure VData (A R T : Subgroup G) (p : G) (J : Subgroup G) (S : Set G) : Prop where
  le : J ≤ A
  mem : p ∈ J
  ne_one : p ≠ 1
  aPart_mem : ∃ t ∈ T, t⁻¹ * p ∈ R
  aPart_le : ∀ t ∈ T, ∀ p' ∈ A, t⁻¹ * p' ∈ R → p' ∈ J
  le_centralizer : ∀ b ∈ A, Commute (b * p * b⁻¹) p →
    J ≤ centralizer ({b * p * b⁻¹} : Set G)
  le_normalizer : A ⊓ centralizer ({p} : Set G) ≤ normalizer (J : Set G)
  trans : ∀ j ∈ S, ∃ a ∈ A ⊓ normalizer (J : Set G), a * p * a⁻¹ = j
  free : ∀ a ∈ A ⊓ normalizer (J : Set G), a * p * a⁻¹ = p → a ∈ centralizer (J : Set G)
  gen : J ≤ closure S
  sylow : ∀ x ∈ A ⊓ centralizer ({p} : Set G), (∀ b ∈ A, Commute (b * p * b⁻¹) p →
    x ∈ centralizer ({b * p * b⁻¹} : Set G)) → (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ J

namespace VData

variable [Finite G] {A R T J : Subgroup G} {p : G} {S : Set G} {g : G}
  (hV : VData A R T p J S) (hc : Sec3 A R T g)
include hV hc

omit [Finite G] hc in
theorem subset : S ⊆ J := by
  intro j hj
  obtain ⟨a, ha, rfl⟩ := hV.trans j hj
  exact (mem_normalizer_iff.mp (mem_inf.mp ha).2 p).mp hV.mem

variable (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
include h32 h4 h34

theorem exists_mul_of_mem {z s : G}
    (hz : rightConjugate R z ≤ centralizer ((R ⊔ T : Subgroup G) : Set G))
    (hs : s ∈ rightConjugate R z) : ∃ r ∈ R, r⁻¹ * s ∈ A ⊓ centralizer (J : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSR : rightConjugate R z ≤ centralizer (R : Set G) :=
    hz.trans (centralizer_le fun r hr => mem_sup_left hr)
  have hSAK := conj_le_sup_centralizer (lemma33Two_of h32 h4 h34) hc.hyp hc.sylowR ⟨z, rfl⟩ hSR
  have hRS : IsPGroup 2 ↥(R ⊔ rightConjugate R z) :=
    IsPGroup.to_sup_of_normal_left' hc.sylowR.isPGroup (hc.sylowR.isPGroup.map _)
      (hSR.trans (centralizer_le_normalizer _))
  have hle := le_sup_of_isSylowOf (centralizer_le_normalizer _) hc.sylowR le_sup_left hRS
    (sup_le (hc.sylowR.le.trans le_sup_right) hSAK)
  have hRA : R ≤ normalizer (A : Set G) := hc.sylowR.le.trans (centralizer_le_normalizer _)
  have hs' : s ∈ ((R ⊔ A : Subgroup G) : Set G) := hle (mem_sup_right hs)
  rw [coe_mul_of_left_le_normalizer_right R A hRA] at hs'
  obtain ⟨r, hr, a, ha, rfl⟩ := hs'
  refine ⟨r, hr, ?_⟩
  rw [inv_mul_cancel_left]
  obtain ⟨t, ht, hρ⟩ := hV.aPart_mem
  have hsC := hz hs
  have hst : Commute (r * a) t :=
    (mem_centralizer_iff.mp hsC t (mem_sup_right ht)).symm
  have hsρ : Commute (r * a) (t⁻¹ * p) :=
    (mem_centralizer_iff.mp hsC _ (mem_sup_left hρ)).symm
  have hrt : Commute r t := (hc.commute_T_R ht hr).symm
  have hrρ : Commute r (t⁻¹ * p) := hc.commute_R h32 hr hρ
  have hat : Commute a t := by
    have h1 : Commute (r⁻¹ * (r * a)) t := (hrt.inv_left).mul_left hst
    rwa [inv_mul_cancel_left] at h1
  have haρ : Commute a (t⁻¹ * p) := by
    have h1 : Commute (r⁻¹ * (r * a)) (t⁻¹ * p) := (hrρ.inv_left).mul_left hsρ
    rwa [inv_mul_cancel_left] at h1
  have hap : Commute a p := by
    have h1 : Commute a (t * (t⁻¹ * p)) := hat.mul_right haρ
    rwa [mul_inv_cancel_left] at h1
  have haN : a ∈ normalizer (J : Set G) :=
    hV.le_normalizer (mem_inf.mpr ⟨ha, mem_centralizer_singleton_iff.mpr hap.eq⟩)
  refine mem_inf.mpr ⟨ha, hV.free a (mem_inf.mpr ⟨ha, haN⟩) ?_⟩
  rw [hap.eq, mul_inv_cancel_right]

theorem exists_aPart_mem {t : G} (ht : t ∈ T) : ∃ p' ∈ J, t⁻¹ * p' ∈ R := by
  obtain ⟨p', hp'A, hρ'⟩ := hc.exists_aPart h32 h4 h34 ht
  exact ⟨p', hV.aPart_le t ht p' hp'A hρ', hρ'⟩

theorem rightConjugate_le_centralizer {b : G} (hb : b ∈ A ⊓ normalizer (J : Set G)) :
    rightConjugate T b ≤ centralizer (sec3W R T : Set G) := by
  rw [le_centralizer_iff]
  refine iSup₂_le fun z hz => ?_
  intro s hs
  rw [mem_centralizer_iff]
  intro u hu
  obtain ⟨r, hr, hra⟩ := hV.exists_mul_of_mem hc h32 h4 h34 hz hs
  obtain ⟨haA, haJ⟩ := mem_inf.mp hra
  rw [SetLike.mem_coe, mem_rightConjugate_iff] at hu
  obtain ⟨p', hp'J, hρ'⟩ := hV.exists_aPart_mem hc h32 h4 h34 hu
  obtain ⟨hbA, hbJ⟩ := mem_inf.mp hb
  have hj : b⁻¹ * p' * b ∈ J := by
    have := (mem_normalizer_iff.mp (inv_mem hbJ) p').mp hp'J
    simpa using this
  have hbρ : Commute b ((b * u * b⁻¹)⁻¹ * p') := hc.commute_of_mem hbA hρ'
  have hu' : u = (b⁻¹ * p' * b) * ((b * u * b⁻¹)⁻¹ * p')⁻¹ := by
    have h1 : b⁻¹ * ((b * u * b⁻¹)⁻¹ * p')⁻¹ * b = ((b * u * b⁻¹)⁻¹ * p')⁻¹ := by
      rw [mul_assoc, ← hbρ.inv_right.eq, inv_mul_cancel_left]
    calc u = b⁻¹ * p' * (((b * u * b⁻¹)⁻¹ * p')⁻¹) * b := by group
      _ = (b⁻¹ * p' * b) * (b⁻¹ * ((b * u * b⁻¹)⁻¹ * p')⁻¹ * b) := by group
      _ = _ := by rw [h1]
  have hs' : s = r * (r⁻¹ * s) := by group
  have hjr : Commute (b⁻¹ * p' * b) r := hc.commute_of_mem (hV.le hj) hr
  have hja : Commute (b⁻¹ * p' * b) (r⁻¹ * s) :=
    mem_centralizer_iff.mp haJ _ hj
  have hρr : Commute ((b * u * b⁻¹)⁻¹ * p')⁻¹ r :=
    (hc.commute_R h32 hρ' hr).inv_left
  have hρa : Commute ((b * u * b⁻¹)⁻¹ * p')⁻¹ (r⁻¹ * s) :=
    ((hc.commute_of_mem haA hρ').symm).inv_left
  have hcomm : Commute ((b⁻¹ * p' * b) * ((b * u * b⁻¹)⁻¹ * p')⁻¹) (r * (r⁻¹ * s)) :=
    (hjr.mul_right hja).mul_left (hρr.mul_right hρa)
  rw [← hs', ← hu'] at hcomm
  exact hcomm.eq

theorem rightConjugate_le_sec3V {b : G} (hb : b ∈ A ⊓ normalizer (J : Set G)) :
    rightConjugate T b ≤ sec3V R T := by
  obtain ⟨w, hw⟩ := hc.exists_conj
  have h := hV.rightConjugate_le_centralizer hc h32 h4 h34 hb
  rw [hw, rightConjugate_mul] at h ⊢
  exact le_sec3V h

theorem le_inf_sec3V : J ≤ sec3V R T ⊓ A := by
  obtain ⟨w, hw⟩ := hc.exists_conj
  have hRV : R ≤ sec3V R T := le_sup_left.trans (le_sec3V_of ⟨w, hw⟩)
  have hS : S ⊆ sec3V R T := by
    intro j hj
    obtain ⟨a, ha, rfl⟩ := hV.trans j hj
    obtain ⟨t, ht, hρ⟩ := hV.aPart_mem
    have haA : a ∈ A := (mem_inf.mp ha).1
    have ha' : a⁻¹ ∈ A ⊓ normalizer (J : Set G) :=
      mem_inf.mpr ⟨inv_mem haA, inv_mem (mem_inf.mp ha).2⟩
    have hat : a * t * a⁻¹ ∈ sec3V R T := by
      apply hV.rightConjugate_le_sec3V hc h32 h4 h34 ha'
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using ht
    have hcomm : Commute a (t⁻¹ * p) := hc.commute_of_mem haA hρ
    have h1 : a * p * a⁻¹ = (a * t * a⁻¹) * (t⁻¹ * p) := by
      calc a * p * a⁻¹ = a * t * (t⁻¹ * p) * a⁻¹ := by group
        _ = a * t * (a⁻¹ * (a * (t⁻¹ * p) * a⁻¹)) := by group
        _ = (a * t * a⁻¹) * (t⁻¹ * p) := by rw [hcomm.eq]; group
    rw [h1]
    exact mul_mem hat (hRV hρ)
  exact le_inf (hV.gen.trans ((closure_le _).mpr hS)) hV.le

theorem inf_sec3V_le : sec3V R T ⊓ A ≤ J := by
  obtain ⟨w, hw⟩ := hc.exists_conj
  have hVe : IsElemAbelian 2 (sec3V R T) :=
    isElemAbelian_sec3V (hc.elemR h32) hc.le_centralizer ⟨w, hw⟩
  have hJV := hV.le_inf_sec3V hc h32 h4 h34
  obtain ⟨t, ht, hρ⟩ := hV.aPart_mem
  intro v hv
  obtain ⟨hvV, hvA⟩ := mem_inf.mp hv
  have hcommV : ∀ x ∈ sec3V R T, Commute v x := fun x hx =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨v, hvV⟩ ⟨x, hx⟩)
  have hvp : v ∈ centralizer ({p} : Set G) :=
    mem_centralizer_singleton_iff.mpr (hcommV p (mem_inf.mp (hJV hV.mem)).1).eq
  have hvΔ : ∀ b ∈ A, Commute (b * p * b⁻¹) p →
      v ∈ centralizer ({b * p * b⁻¹} : Set G) := by
    intro b hbA hbp
    have hJb : ∀ j ∈ J, Commute (b * j * b⁻¹) p := by
      intro j hj
      have hc' : Commute (b⁻¹ * p * b⁻¹⁻¹) p := by
        have h1 : Commute (b⁻¹ * (b * p * b⁻¹) * b) (b⁻¹ * p * b) := by
          have := (hbp.conj b⁻¹)
          simpa [mul_assoc] using this
        simpa [mul_assoc] using h1.symm
      have hj' := mem_centralizer_singleton_iff.mp (hV.le_centralizer b⁻¹ (inv_mem hbA) hc' hj)
      have h2 : Commute j (b⁻¹ * p * b) := by
        simp only [inv_inv] at hj'
        exact hj'
      have h3 := h2.conj b
      simpa [mul_assoc] using h3
    have hSc : S ⊆ ((centralizer (J : Set G)).comap (MulAut.conj b).toMonoidHom : Set G) := by
      intro j₀ hj₀
      obtain ⟨a, ha, rfl⟩ := hV.trans j₀ hj₀
      have hba : b * (a * p * a⁻¹) * b⁻¹ = (b * a) * p * (b * a)⁻¹ := by group
      have hc2 : Commute ((b * a) * p * (b * a)⁻¹) p := by
        rw [← hba]
        exact hJb _ (hV.subset hj₀)
      have h1 := hV.le_centralizer (b * a) (mul_mem hbA (mem_inf.mp ha).1) hc2
      rw [SetLike.mem_coe, mem_comap]
      change b * (a * p * a⁻¹) * b⁻¹ ∈ centralizer (J : Set G)
      rw [hba, mem_centralizer_iff]
      intro j hj
      exact mem_centralizer_singleton_iff.mp (h1 hj)
    have hJJ : ∀ j ∈ J, ∀ j₀ ∈ J, Commute j (b * j₀ * b⁻¹) := by
      intro j hj j₀ hj₀
      have h1 : b * j₀ * b⁻¹ ∈ centralizer (J : Set G) := (closure_le _).mpr hSc (hV.gen hj₀)
      exact mem_centralizer_iff.mp h1 j hj
    have hT'W : rightConjugate T b⁻¹ ≤ sec3W R T := by
      have hcen : rightConjugate T b⁻¹ ≤ centralizer ((R ⊔ T : Subgroup G) : Set G) := by
        refine le_centralizer_sup ?_ ?_
        · intro u hu
          rw [mem_centralizer_iff]
          intro r hr
          rw [mem_rightConjugate_iff, inv_inv] at hu
          have hbr : Commute b r := hc.commute_of_mem hbA hr
          have h1 : Commute (b * (b⁻¹ * u * b) * b⁻¹) r :=
            (hbr.mul_left (hc.commute_T_R hu hr)).mul_left hbr.inv_left
          rw [show b * (b⁻¹ * u * b) * b⁻¹ = u by group] at h1
          exact h1.eq.symm
        · intro u hu
          rw [mem_centralizer_iff]
          intro t'' ht''
          rw [mem_rightConjugate_iff, inv_inv] at hu
          obtain ⟨p', hp'J, hρ'⟩ := hV.exists_aPart_mem hc h32 h4 h34 hu
          obtain ⟨p'', hp''J, hρ''⟩ := hV.exists_aPart_mem hc h32 h4 h34 ht''
          set t' := b⁻¹ * u * b with ht'
          have hu' : u = (b * p' * b⁻¹) * (t'⁻¹ * p')⁻¹ := by
            have hbρ : Commute b (t'⁻¹ * p') := hc.commute_of_mem hbA hρ'
            calc u = b * t' * b⁻¹ := by rw [ht']; group
              _ = b * p' * (t'⁻¹ * p')⁻¹ * b⁻¹ := by group
              _ = (b * p' * b⁻¹) * (b * (t'⁻¹ * p')⁻¹ * b⁻¹) := by group
              _ = _ := by rw [hbρ.inv_right.eq, mul_inv_cancel_right]
          have ht''' : t'' = p'' * (t''⁻¹ * p'')⁻¹ := by group
          have hbp'A : b * p' * b⁻¹ ∈ A := mul_mem (mul_mem hbA (hV.le hp'J)) (inv_mem hbA)
          have h1 : Commute (b * p' * b⁻¹) p'' := (hJJ p'' hp''J p' hp'J).symm
          have h2 : Commute (b * p' * b⁻¹) (t''⁻¹ * p'')⁻¹ :=
            (hc.commute_of_mem hbp'A hρ'').inv_right
          have h3 : Commute (t'⁻¹ * p')⁻¹ p'' :=
            ((hc.commute_of_mem (hV.le hp''J) hρ').symm).inv_left
          have h4' : Commute (t'⁻¹ * p')⁻¹ (t''⁻¹ * p'')⁻¹ :=
            (hc.commute_R h32 hρ' hρ'').inv_inv
          have h5 : Commute ((b * p' * b⁻¹) * (t'⁻¹ * p')⁻¹) (p'' * (t''⁻¹ * p'')⁻¹) :=
            (h1.mul_right h2).mul_left (h3.mul_right h4')
          rw [← hu', ← ht'''] at h5
          exact h5.eq.symm
      rw [hw, rightConjugate_mul] at hcen ⊢
      exact le_sec3W hcen
    have hbt : b * t * b⁻¹ ∈ rightConjugate T b⁻¹ := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using ht
    have hvbt : Commute v (b * t * b⁻¹) :=
      (mem_centralizer_iff.mp (sec3V_le_centralizer R T hvV) _ (hT'W hbt)).symm
    have hvρ : Commute v (t⁻¹ * p) := hc.commute_of_mem hvA hρ
    have hbρ : Commute b (t⁻¹ * p) := hc.commute_of_mem hbA hρ
    have hbp' : b * p * b⁻¹ = (b * t * b⁻¹) * (t⁻¹ * p) := by
      calc b * p * b⁻¹ = b * t * (t⁻¹ * p) * b⁻¹ := by group
        _ = (b * t * b⁻¹) * (b * (t⁻¹ * p) * b⁻¹) := by group
        _ = _ := by rw [hbρ.eq, mul_inv_cancel_right]
    rw [mem_centralizer_singleton_iff, hbp']
    exact (hvbt.mul_right hvρ).eq
  have hv2 : v ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    exact hVe.2 v hvV
  exact hV.sylow v (mem_inf.mpr ⟨hvA, hvp⟩) hvΔ ⟨1, hv2⟩

theorem inf_sec3V_eq : sec3V R T ⊓ A = J :=
  le_antisymm (hV.inf_sec3V_le hc h32 h4 h34) (hV.le_inf_sec3V hc h32 h4 h34)

theorem sec3V_eq_sup : sec3V R T = R ⊔ J := by
  have h := (lemma35 h32 (lemma33Two_of h32 h4 h34) hc.hyp hc.sylowR hc.sylowT
    hc.le_centralizer).2.1
  rwa [hV.inf_sec3V_eq hc h32 h4 h34] at h

end VData

end CFSG.ComponentClassification.RankTwoClassical
