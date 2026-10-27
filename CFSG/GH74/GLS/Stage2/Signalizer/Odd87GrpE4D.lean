module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Img
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4CGlue
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Ncl
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4L34
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt43E

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement Pointwise

@[expose] def L34DiagClosure : Prop :=
  ∀ (A : Type) [Group A] (J : Subgroup A) [J.Normal], LieModel ↥J .PSL 3 2 2 →
    ∀ X : Subgroup A, Nat.card ↥X = 3 → (J ⊔ centralizer (J : Set A) ⊔ X).Normal

section

variable {G : Type} [Group G] {z : G} {k : Kind}
variable {A : Type} [Group A] [Finite A] {a : A} {p : ℕ} {X J : Subgroup A}

theorem C43d1_of_eq {K : Subgroup A} (hK : ncl X = K) (hk : k = Kind.mcl ∨ k = Kind.ly)
    (h3 : Nat.card ↥X = 3) (h4 : IsPGL3Four ↥K)
    (h5 : K ⊓ centralizer ({a} : Set A) = ⁅K, K⁆ ⊓ centralizer (X : Set A))
    (h6 : IVK.IsL2 ↥(K ⊓ centralizer ({a} : Set A)) (fun q => q = 4))
    (h7 : (K ⊔ zpowers a) ⊓ centralizer ((K ⊓ centralizer ({a} : Set A) : Subgroup A) : Set A) =
      X ⊔ zpowers a) : C43d1 k a X := by
  subst hK
  exact ⟨hk, h3, h4, h5, h6, h7⟩

theorem secMk_comm_iff (hN : pPrimeCore 2 ↥(secY a X J) = ⊥) {y y' : A} (hy : y ∈ secY a X J)
    (hy' : y' ∈ secY a X J) :
    secMk a X J y hy * secMk a X J y' hy' = secMk a X J y' hy' * secMk a X J y hy ↔ y * y' = y' * y := by
  rw [← secMk_mul hy hy', ← secMk_mul hy' hy, secMk_inj hN]

theorem comm_of_card_three {X : Subgroup A} (h3 : Nat.card ↥X = 3) :
    ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
  haveI : Fact (Nat.Prime (Nat.card ↥X)) := ⟨by rw [h3]; exact Nat.prime_three⟩
  haveI : IsCyclic ↥X := isCyclic_of_prime_card rfl
  letI : CommGroup ↥X := IsCyclic.commGroup
  intro x hx y hy
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥X) ⟨y, hy⟩)

theorem inf_centralizer_eq_bot_of_card_three {X : Subgroup A} {a : A} (h3 : Nat.card ↥X = 3)
    (hcomm : ⁅X, zpowers a⁆ = X) (hne : X ≠ ⊥) (ha2 : a * a = 1) :
    X ⊓ centralizer ({a} : Set A) = ⊥ := by
  haveI : Fact (Nat.Prime (Nat.card ↥X)) := ⟨by rw [h3]; exact Nat.prime_three⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((X ⊓ centralizer ({a} : Set A)).subgroupOf X)
    with h | h
  · exact (Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le inf_le_left
  · exfalso
    apply hne
    have hle : X ≤ X ⊓ centralizer ({a} : Set A) := Subgroup.subgroupOf_eq_top.mp h
    rw [← hcomm, eq_bot_iff, Subgroup.commutator_le]
    intro x hx w hw
    rcases mem_zpowers_involution ha2 hw with rfl | rfl
    · simp
    · have h' := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hle hx)).2
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.mpr h'

theorem case_d (F : E4Hyp G z k) (hOut : L34DiagClosure) {c : E4Ctx G z A a p X} (d : SubData c J)
    (hd : C42d k (secZ a X J) (secX a X J) (secJ a X J)) : C43d1 k a X := by
  have : Fact p.Prime := ⟨c.A4.prime⟩
  obtain ⟨hk, hPGL, hLie, hX3, hCzCX, hL2, hCent⟩ := hd
  have hLieHat : LieModel (Hat J) .PSL 3 2 2 :=
    Transport.lieModel_of_mulEquiv (secJ_equiv d.hyp).some hLie
  have hf : ∀ c' : A, orderOf c' = 2 → c' ∈ centralizer (J : Set A) → False :=
    fun c' h1 h2 => F.f3 A a c.sec J d.comp 2 2 Nat.prime_two (by norm_num) (Or.inr (by norm_num))
      hLieHat c' h1 h2
  have hcomp1 : ∀ J' : Subgroup A, IsComponent J' → J' = J := fun J' hJ' =>
    comp_eq_of_no_invol d.comp hf hJ'
  have hcomp : ∀ J' : Subgroup A, IsComponent J' → J' ≤ ncl X → J' = J := fun J' hJ' _ => hcomp1 J' hJ'
  have hJn : J.Normal := normal_of_unique d.comp hcomp1
  have hR2 : pCore 2 A = ⊥ := pCore_two_eq_bot_of_no_invol d.comp hf
  have hF : ∀ q : ℕ, q.Prime → X ≤ centralizer ((pCore q A : Subgroup A) : Set A) := by
    intro q hq
    by_cases hq2 : q = 2
    · subst hq2
      rw [hR2]
      intro x _ y hy
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
      subst hy
      simp
    · exact c.a41 q hq hq2
  have hJK : J ≤ ncl X := comp_le_ncl d.comp d.JX
  have hXY : X ≤ secY a X J := X_le_secY a X J
  have hJY : J ≤ secY a X J := J_le_secY a X J
  have hp3 : p = 3 := by
    obtain ⟨n, hn⟩ := (secB_Sig4A d.hyp).pgroup.exists_card_eq
    rw [hX3] at hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at hn
    have hdvd : p ∣ p ^ n := dvd_pow_self p hn0
    rw [← hn] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq c.A4.prime Nat.prime_three).mp hdvd
  have hcop3 : Nat.Coprime 3 (Nat.card (pPrimeCore 2 ↥J)) := by
    have h1 := secPsi_ker_coprime d.hyp hJn c.op
    rw [secPsi_ker_eq d.hyp, hp3] at h1
    exact h1
  have hN1' : pPrimeCore 2 ↥J = ⊥ := pPrimeCore_eq_bot_of_l34 d.comp.1 hLieHat hcop3
  have hN1 : pPrimeCoreOf 2 J = ⊥ := by
    unfold pPrimeCoreOf
    rw [hN1', Subgroup.map_bot]
  have hker : (secPsi a X J).ker = ⊥ := secPsi_ker_eq_bot d.hyp hN1
  have hXC : X ⊓ centralizer (J : Set A) = ⊥ := by
    have hb := c.b41
    rw [hR2, bot_sup_eq, layer_eq_of_unique d.comp hcomp1] at hb
    exact hb
  have hX3A : Nat.card ↥X = 3 := (card_X_eq_secX_of_chi d.hyp hXC).trans hX3
  have hKX : secX a X J ⊓ secJ a X J = ⊥ := by
    haveI : Fact (Nat.Prime (Nat.card ↥(secX a X J))) := ⟨by rw [hX3]; exact Nat.prime_three⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card
      ((secX a X J ⊓ secJ a X J).subgroupOf (secX a X J)) with h | h
    · exact (Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le inf_le_left
    · exfalso
      have hXK : secX a X J ≤ secJ a X J := (Subgroup.subgroupOf_eq_top.mp h).trans inf_le_right
      have hsup : secJ a X J ⊔ secX a X J = secJ a X J := sup_eq_left.mpr hXK
      rw [hsup] at hPGL
      have h3 := card_pgl3_four_eq hPGL hLie
      have hpos : 0 < Nat.card ↥(secJ a X J) := Nat.card_pos
      omega
  have hN : pPrimeCore 2 ↥(secY a X J) = ⊥ := pPrimeCore_secY_eq_bot d hJn hker hXC hKX
  have hLieJ : LieModel ↥J .PSL 3 2 2 :=
    Transport.lieModel_of_mulEquiv (secPsiEquiv d.hyp hN1).symm hLie
  have hP : (J ⊔ centralizer (J : Set A) ⊔ X).Normal := by
    haveI := hJn
    exact hOut A J hLieJ X hX3A
  have hncl : ncl X = J ⊔ X :=
    ncl_eq_sup_of_normal c.A4.prime c.A4.pgroup c.op d.comp hJn hJK hcomp hF hP
  have hMY : J ⊔ X ≤ secY a X J := sup_le hJY hXY
  have hJX : J ⊓ X = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hx' := Subgroup.mem_inf.mp hx
    have h1 : secMk a X J x (hXY hx'.2) ∈ secX a X J ⊓ secJ a X J :=
      Subgroup.mem_inf.mpr ⟨secMk_mem_secX hx'.2, secMk_mem_secJ hx'.1⟩
    rw [hKX, Subgroup.mem_bot] at h1
    exact (secMk_inj hN (hXY hx'.2) (secY a X J).one_mem).mp (h1.trans secMk_one.symm)
  have hCXa : X ⊓ centralizer ({a} : Set A) = ⊥ :=
    inf_centralizer_eq_bot_of_card_three hX3A c.A4.comm c.A4.ne_bot c.z2
  have hXcomm := comm_of_card_three hX3A
  have hperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp d.comp.1.1
  have hJX' : ((J ⊔ X : Subgroup A) : Set A) = (J : Set A) * (X : Set A) := Subgroup.normal_mul J X
  have hKK : ⁅J ⊔ X, J ⊔ X⁆ = J := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro k₁ hk₁ k₂ hk₂
      have hk₁' : k₁ ∈ (J : Set A) * (X : Set A) := by rw [← hJX']; exact hk₁
      have hk₂' : k₂ ∈ (J : Set A) * (X : Set A) := by rw [← hJX']; exact hk₂
      obtain ⟨j₁, hj₁, x₁, hx₁, rfl⟩ := hk₁'
      obtain ⟨j₂, hj₂, x₂, hx₂, rfl⟩ := hk₂'
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement]
      have hj1 : QuotientGroup.mk' J j₁ = 1 := (QuotientGroup.eq_one_iff j₁).mpr hj₁
      have hj2 : QuotientGroup.mk' J j₂ = 1 := (QuotientGroup.eq_one_iff j₂).mpr hj₂
      have e1 : QuotientGroup.mk' J (j₁ * x₁) = QuotientGroup.mk' J x₁ := by
        rw [map_mul, hj1, one_mul]
      have e2 : QuotientGroup.mk' J (j₂ * x₂) = QuotientGroup.mk' J x₂ := by
        rw [map_mul, hj2, one_mul]
      show ⁅QuotientGroup.mk' J (j₁ * x₁), QuotientGroup.mk' J (j₂ * x₂)⁆ = 1
      rw [e1, e2, ← map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm.mpr (hXcomm x₁ hx₁ x₂ hx₂), map_one]
    · calc J = ⁅J, J⁆ := hperf.symm
        _ ≤ ⁅J ⊔ X, J ⊔ X⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
  have hKa : (J ⊔ X) ⊓ centralizer ({a} : Set A) = J ⊓ centralizer ({a} : Set A) := by
    apply le_antisymm
    · intro k hk
      obtain ⟨hkK, hkC⟩ := Subgroup.mem_inf.mp hk
      have hk' : k ∈ (J : Set A) * (X : Set A) := by rw [← hJX']; exact hkK
      obtain ⟨j, hj, x, hx, rfl⟩ := hk'
      have hkC' : j * x * a = a * (j * x) := Subgroup.mem_centralizer_singleton_iff.mp hkC
      have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right c.z2
      have haJ' : a * j * a⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp d.zJ j).mp hj
      have haX' : a * x * a⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp c.a_mem_normalizer x).mp hx
      have h1 : (a * j * a⁻¹) * (a * x * a⁻¹) = j * x := by
        calc (a * j * a⁻¹) * (a * x * a⁻¹) = a * (j * x) * a⁻¹ := by group
          _ = j * x := by rw [← hkC']; group
      have h2 : (j⁻¹ * (a * j * a⁻¹)) = x * (a * x * a⁻¹)⁻¹ := by
        have := congrArg (fun t => j⁻¹ * t * (a * x * a⁻¹)⁻¹) h1
        simpa [mul_assoc] using this
      have h3 : x * (a * x * a⁻¹)⁻¹ ∈ J ⊓ X :=
        Subgroup.mem_inf.mpr ⟨h2 ▸ mul_mem (inv_mem hj) haJ', mul_mem hx (inv_mem haX')⟩
      rw [hJX, Subgroup.mem_bot, mul_inv_eq_one] at h3
      have h4 : x ∈ X ⊓ centralizer ({a} : Set A) := by
        refine Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        calc x * a = (a * x * a⁻¹) * a := by rw [← h3]
          _ = a * x := by group
      rw [hCXa, Subgroup.mem_bot] at h4
      subst h4
      refine Subgroup.mem_inf.mpr ⟨by simpa using hj, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      simpa using hkC'
    · exact inf_le_inf_right _ le_sup_left
  have hJaX : J ⊓ centralizer ({a} : Set A) = J ⊓ centralizer (X : Set A) := by
    apply le_antisymm
    · intro j hj
      obtain ⟨hjJ, hjC⟩ := Subgroup.mem_inf.mp hj
      have hjC' : j * a = a * j := Subgroup.mem_centralizer_singleton_iff.mp hjC
      have hjY : j ∈ secY a X J := hJY hjJ
      have h1 : secMk a X J j hjY ∈ secJ a X J ⊓ centralizer ({secZ a X J} : Set (secB a X J)) :=
        Subgroup.mem_inf.mpr ⟨secMk_mem_secJ hjJ, Subgroup.mem_centralizer_singleton_iff.mpr
          ((secMk_comm_iff hN hjY (z_mem_secY a X J)).mpr hjC')⟩
      rw [hCzCX] at h1
      refine Subgroup.mem_inf.mpr ⟨hjJ, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp h1).2 _ (secMk_mem_secX hx)
      exact (secMk_comm_iff hN (hXY hx) hjY).mp this
    · intro j hj
      obtain ⟨hjJ, hjC⟩ := Subgroup.mem_inf.mp hj
      have hjY : j ∈ secY a X J := hJY hjJ
      have h1 : secMk a X J j hjY ∈
          secJ a X J ⊓ centralizer ((secX a X J : Subgroup (secB a X J)) : Set (secB a X J)) := by
        refine Subgroup.mem_inf.mpr ⟨secMk_mem_secJ hjJ, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        obtain ⟨x, hx, rfl⟩ := mem_secX_iff.mp hb
        exact (secMk_comm_iff hN (hXY hx) hjY).mpr (Subgroup.mem_centralizer_iff.mp hjC x hx)
      rw [← hCzCX] at h1
      refine Subgroup.mem_inf.mpr ⟨hjJ, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      exact (secMk_comm_iff hN hjY (z_mem_secY a X J)).mp
        (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp h1).2)
  have hIsPGL : IsPGL3Four ↥(J ⊔ X) := by
    have himg : secImg a X J (J ⊔ X) = secJ a X J ⊔ secX a X J := secImg_sup hJY hXY
    have e := secImgEquiv hN hMY
    rw [himg] at e
    exact Transport.isPGL3Four_of_mulEquiv e.symm hPGL
  have hSa : J ⊓ centralizer ({a} : Set A) ≤ secY a X J := inf_le_left.trans hJY
  have himgCa : secImg a X J (J ⊓ centralizer ({a} : Set A)) =
      secJ a X J ⊓ centralizer ({secZ a X J} : Set (secB a X J)) := by
    ext b
    constructor
    · intro hb
      obtain ⟨s, hs, rfl⟩ := (mem_secImg_iff hSa).mp hb
      obtain ⟨hsJ, hsC⟩ := Subgroup.mem_inf.mp hs
      exact Subgroup.mem_inf.mpr ⟨secMk_mem_secJ hsJ, Subgroup.mem_centralizer_singleton_iff.mpr
        ((secMk_comm_iff hN (hJY hsJ) (z_mem_secY a X J)).mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hsC))⟩
    · intro hb
      obtain ⟨hbJ, hbC⟩ := Subgroup.mem_inf.mp hb
      obtain ⟨j, hj, rfl⟩ := mem_secJ_iff.mp hbJ
      refine (mem_secImg_iff hSa).mpr ⟨j, Subgroup.mem_inf.mpr ⟨hj, ?_⟩, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((secMk_comm_iff hN (J_le_secY a X J hj) (z_mem_secY a X J)).mp
          (Subgroup.mem_centralizer_singleton_iff.mp hbC))
  have hIsL2 : IVK.IsL2 ↥(J ⊓ centralizer ({a} : Set A)) (fun q => q = 4) := by
    have e := secImgEquiv hN hSa
    rw [himgCa] at e
    exact Transport.isL2_of_mulEquiv e.symm hL2
  have hXZ : X ⊔ zpowers a ≤ secY a X J := sup_le hXY (zpowers_le.mpr (z_mem_secY a X J))
  have hcentr : (J ⊔ X ⊔ zpowers a) ⊓ centralizer ((J ⊓ centralizer ({a} : Set A) : Subgroup A) : Set A) =
      X ⊔ zpowers a := by
    apply le_antisymm
    · intro y hy
      obtain ⟨hyY, hyC⟩ := Subgroup.mem_inf.mp hy
      have hy' : y ∈ secY a X J := hyY
      have h1 : secMk a X J y hy' ∈ secJ a X J ⊔ secX a X J ⊔ zpowers (secZ a X J) := by
        have himgY : secImg a X J (secY a X J) = secJ a X J ⊔ secX a X J ⊔ zpowers (secZ a X J) := by
          show secImg a X J (J ⊔ X ⊔ zpowers a) = _
          rw [secImg_sup (sup_le hJY hXY) (zpowers_le.mpr (z_mem_secY a X J)), secImg_sup hJY hXY,
            secImg_zpowers]
          rfl
        have : secMk a X J y hy' ∈ secImg a X J (secY a X J) :=
          (mem_secImg_iff le_rfl).mpr ⟨y, hy', rfl⟩
        rwa [himgY] at this
      have h2 : secMk a X J y hy' ∈ centralizer
          ((secJ a X J ⊓ centralizer ({secZ a X J} : Set (secB a X J)) : Subgroup (secB a X J)) :
            Set (secB a X J)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        obtain ⟨hbJ, hbC⟩ := Subgroup.mem_inf.mp hb
        obtain ⟨j, hj, rfl⟩ := mem_secJ_iff.mp hbJ
        have hjC : j ∈ centralizer ({a} : Set A) :=
          Subgroup.mem_centralizer_singleton_iff.mpr
            ((secMk_comm_iff hN (J_le_secY a X J hj) (z_mem_secY a X J)).mp
              (Subgroup.mem_centralizer_singleton_iff.mp hbC))
        have := Subgroup.mem_centralizer_iff.mp hyC j (Subgroup.mem_inf.mpr ⟨hj, hjC⟩)
        exact (secMk_comm_iff hN (J_le_secY a X J hj) hy').mpr this
      have h3 : secMk a X J y hy' ∈ secX a X J ⊔ zpowers (secZ a X J) := by
        rw [← hCent]
        exact Subgroup.mem_inf.mpr ⟨h1, h2⟩
      have himgXZ : secImg a X J (X ⊔ zpowers a) = secX a X J ⊔ zpowers (secZ a X J) := by
        rw [secImg_sup hXY (zpowers_le.mpr (z_mem_secY a X J)), secImg_zpowers]
        rfl
      rw [← himgXZ, mem_secImg_iff hXZ] at h3
      obtain ⟨w, hw, hyw⟩ := h3
      have := (secMk_inj hN hy' (hXZ hw)).mp hyw
      rw [this]
      exact hw
    · refine le_inf (sup_le (le_sup_right.trans le_sup_left) le_sup_right) (sup_le ?_ ?_)
      · intro x hx
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro i hi
        have hi' := (hJaX ▸ hi : i ∈ J ⊓ centralizer (X : Set A))
        have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hi').2 x hx
        exact this.symm
      · intro w hw
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro i hi
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        exact ((Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp
          (Subgroup.mem_inf.mp hi).2) m)).eq
  refine C43d1_of_eq hncl hk hX3A hIsPGL ?_ ?_ ?_
  · rw [hKK, hKa, hJaX]
  · rw [hKa]; exact hIsL2
  · rw [hKa]; exact hcentr

end

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
