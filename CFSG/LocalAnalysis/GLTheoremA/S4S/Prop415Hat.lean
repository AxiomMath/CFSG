module

public import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Setup
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.Section2.CoprimeTools
public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Common
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def frat2 (R : Subgroup G) : Subgroup G :=
  ⁅R, R⁆ ⊔ Subgroup.closure {g : G | ∃ r ∈ R, g = r ^ 2}

@[expose] def hatN (Rs A : Subgroup G) : Subgroup G :=
  frat2 Rs ⊔ (Rs ⊓ Subgroup.centralizer (A : Set G))

theorem commutator_le_frat2 (R : Subgroup G) : (⁅R, R⁆ : Subgroup G) ≤ frat2 R := le_sup_left

theorem sq_mem_frat2 {R : Subgroup G} {r : G} (hr : r ∈ R) : r ^ 2 ∈ frat2 R :=
  (le_sup_right : Subgroup.closure {g : G | ∃ r ∈ R, g = r ^ 2} ≤ frat2 R)
    (Subgroup.subset_closure ⟨r, hr, rfl⟩)

theorem frat2_le_hatN (R A : Subgroup G) : frat2 R ≤ hatN R A := le_sup_left

theorem hatN_le (R A : Subgroup G) : hatN R A ≤ R :=
  sup_le (sup_le (commutator_self_le R) ((Subgroup.closure_le R).2 (by
    rintro g ⟨r, hr, rfl⟩
    exact R.pow_mem hr 2))) inf_le_left

theorem le_normalizer_frat2 {X R : Subgroup G} (h : X ≤ Subgroup.normalizer (R : Set G)) :
    X ≤ Subgroup.normalizer (frat2 R : Set G) := by
  have h1 : X ≤ Subgroup.normalizer ((⁅R, R⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator h h
  have h2 : X ≤ Subgroup.normalizer
      ((Subgroup.closure {g : G | ∃ r ∈ R, g = r ^ 2} : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_closure_iff]
    intro x hx g hg
    obtain ⟨r, hr, rfl⟩ := hg
    have hxr : x * r * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 (h hx) r).1 hr
    have e : x * r ^ 2 * x⁻¹ = (x * r * x⁻¹) ^ 2 := by
      simp only [pow_two]
      group
    rw [e]
    exact Subgroup.subset_closure ⟨_, hxr, rfl⟩
  exact le_normalizer_sup h1 h2

private def hatModComm (T N : Subgroup G) (Y : Set G)
    (hTN : T ≤ Subgroup.normalizer (N : Set G)) : Subgroup G where
  carrier := {x | x ∈ T ∧ ∀ y ∈ Y, ⁅x, y⁆ ∈ N}
  one_mem' := ⟨T.one_mem, fun y _ => by
    rw [commutatorElement_one_left]
    exact N.one_mem⟩
  mul_mem' := by
    rintro a b ⟨haT, ha⟩ ⟨hbT, hb⟩
    refine ⟨T.mul_mem haT hbT, fun y hy => ?_⟩
    have hid : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hid]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.1 (hTN haT) _).1 (hb y hy)) (ha y hy)
  inv_mem' := by
    rintro a ⟨haT, ha⟩
    refine ⟨T.inv_mem haT, fun y hy => ?_⟩
    have hid : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a := by
      simp only [commutatorElement_def]
      group
    rw [hid]
    have h1 : a⁻¹ * ((⁅a, y⁆)⁻¹) * a⁻¹⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.1 (hTN (T.inv_mem haT)) _).1 (N.inv_mem (ha y hy))
    simpa using h1

private theorem mem_hatModComm {T N : Subgroup G} {Y : Set G}
    {hTN : T ≤ Subgroup.normalizer (N : Set G)} {x : G} :
    x ∈ hatModComm T N Y hTN ↔ x ∈ T ∧ ∀ y ∈ Y, ⁅x, y⁆ ∈ N := Iff.rfl

private theorem hat_coprime_card {B X : Subgroup G} (hB : Nat.card B = 3 ^ 4)
    (hX : IsPGroup 2 X) : Nat.Coprime (Nat.card B) (Nat.card X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hX.exists_card_eq
  rw [hB, hm]
  exact Nat.Coprime.pow 4 m (by norm_num)

private theorem hat_not_dvd_three {X : Subgroup G} (hX : IsPGroup 2 X) : ¬ 3 ∣ Nat.card X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hX.exists_card_eq
  rw [hm]
  intro hd
  have h3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
  omega

private theorem hat_isSolvable_of_isPGroup {X : Subgroup G} (hX : IsPGroup 2 X) :
    Group.IsSolvable ↥X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥X := hX.isNilpotent
  infer_instance

structure Prop415Pre (B : Subgroup G) (x : G) (D S Ss : Subgroup G) : Prop where
  DB : D ≤ B
  Del : IsElemAbelian 3 D
  Dc : Nat.card D = 9
  S2 : IsPGroup 2 S
  BS : B ≤ Subgroup.normalizer (S : Set G)
  BSS : (⁅B, S⁆ : Subgroup G) = S
  SD : S ≤ Subgroup.centralizer (D : Set G)
  SsS : Ss ≤ S
  BSs : B ≤ Subgroup.normalizer (Ss : Set G)
  Ssx : Ss ≤ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G))
  idx : Nat.card S ≤ 4 * Nat.card Ss
  SSle : (⁅S, S⁆ : Subgroup G) ≤ Ss
  ne : (⁅B, (⁅S, S⁆ : Subgroup G)⁆ : Subgroup G) ≠ ⊥

structure HatSetup (B A T Rs N : Subgroup G) : Prop where
  Bel : IsElemAbelian 3 B
  Bc : Nat.card B = 3 ^ 4
  AB : A ≤ B
  Ael : IsElemAbelian 3 A
  Ac : Nat.card A = 9
  T2 : IsPGroup 2 T
  NR : N ≤ Rs
  RT : Rs ≤ T
  Nn : (N.subgroupOf T).Normal
  Rn : (Rs.subgroupOf T).Normal
  BT : B ≤ Subgroup.normalizer (T : Set G)
  BR : B ≤ Subgroup.normalizer (Rs : Set G)
  BN : B ≤ Subgroup.normalizer (N : Set G)
  Rab : (⁅Rs, Rs⁆ : Subgroup G) ≤ N ∧ ∀ r ∈ Rs, r ^ 2 ∈ N
  cR : ∀ t ∈ T, (∀ r ∈ Rs, ⁅t, r⁆ ∈ N) → t ∈ Rs
  idx : Nat.card T = 4 * Nat.card Rs
  AT : ∀ a ∈ A, ∀ t ∈ T, ⁅a, t⁆ ∈ Rs
  Bnc : ¬ (⁅B, T⁆ : Subgroup G) ≤ Rs
  fpf : ∀ r ∈ Rs, (∀ a ∈ A, ⁅r, a⁆ ∈ N) → r ∈ N

theorem exists_invariant_sylow_ge {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B X R : Subgroup G}
    (hB : IsPGroup p B) (hBX : B ≤ Subgroup.normalizer (X : Set G))
    (hX : Nat.Coprime p (Nat.card X)) (hRX : R ≤ X) (hR2 : IsPGroup 2 R)
    (hBR : B ≤ Subgroup.normalizer (R : Set G)) :
    ∃ R' : Subgroup G, R ≤ R' ∧ R' ≤ X ∧ IsPGroup 2 R' ∧ ¬ 2 ∣ R'.relIndex X ∧
      B ≤ Subgroup.normalizer (R' : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM : ¬ p ∣ Nat.card X := (Nat.Prime.coprime_iff_not_dvd hp).1 hX
  obtain ⟨S, hS, hRS, hBS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing hp
    Nat.prime_two hB hM hBX hRX hR2 hBR
  refine ⟨S, hRS, hS.1, hS.2.1, ?_, hBS⟩
  obtain ⟨P, hP⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hS
  have h1 : S.subgroupOf X = (P : Subgroup X) := by
    rw [← hP]
    exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  have h2 : S.relIndex X = (P : Subgroup X).index := by
    rw [Subgroup.relIndex, h1]
  rw [h2]
  exact P.not_dvd_index

private theorem hat_le_glaPPrimeCoreOf {p : ℕ} (hp : p.Prime) {M W : Subgroup G} (hWM : W ≤ M)
    (hW : M ≤ Subgroup.normalizer (W : Set G)) (hcop : ¬ p ∣ Nat.card W) :
    W ≤ GLAPPrimeCoreOf p M := by
  have hN : (W.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWM).2 hW
  have hc : Nat.card (W.subgroupOf M) = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWM).toEquiv
  have hle : W.subgroupOf M ≤ GLAPPrimeCore p ↥M :=
    le_sSup ⟨hN, by rw [hc]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hcop⟩
  calc W = (W.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hWM).symm
    _ ≤ GLAPPrimeCoreOf p M := Subgroup.map_mono hle

private theorem hat_le_of_isPGroup_two {H Rs X : Subgroup G} (hRsH : Rs ≤ H)
    (hHN : H ≤ Subgroup.normalizer (Rs : Set G)) (hRs2 : IsPGroup 2 Rs)
    (hodd : ¬ 2 ∣ Rs.relIndex H) (hXH : X ≤ H) (hX2 : IsPGroup 2 X) : X ≤ Rs := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := X ⊔ Rs with hY
  have hYH : Y ≤ H := sup_le hXH hRsH
  have hY2 : IsPGroup 2 Y := hX2.to_sup_of_normal_right' hRs2 (hXH.trans hHN)
  have hRsY : Rs ≤ Y := le_sup_right
  have h1 : Rs.relIndex Y * Y.relIndex H = Rs.relIndex H :=
    Subgroup.relIndex_mul_relIndex Rs Y H hRsY hYH
  have h2 : Rs.relIndex Y ∣ Nat.card Y := Subgroup.relIndex_dvd_card Rs Y
  obtain ⟨m, hm⟩ := hY2.exists_card_eq
  rw [hm] at h2
  obtain ⟨k, -, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hk0 : k = 0 := by
    by_contra hne
    apply hodd
    rw [← h1, hk']
    exact Dvd.dvd.mul_right (dvd_pow_self 2 hne) _
  rw [hk0, pow_zero] at hk'
  exact le_sup_left.trans (Subgroup.relIndex_eq_one.1 hk')

theorem exists_P_data {B L J J₁ T₁ : Subgroup G} (hBel : IsElemAbelian 3 B)
    (hBJ : B ≤ Subgroup.normalizer (J : Set G)) (hJJ₁ : J ≤ J₁) (hJ₁L : J₁ ≤ L)
    (hBJ₁ : B ≤ Subgroup.normalizer (J₁ : Set G)) (hcov : J₁ ≤ J ⊔ GLAPPrimeCoreOf 3 L)
    (hO₁ : GLAPPrimeCoreOf 3 J₁ ≤ GLAPPrimeCoreOf 3 L) (hT₁J : T₁ ≤ J₁) (hT₁2 : IsPGroup 2 T₁)
    (hBT₁ : B ≤ Subgroup.normalizer (T₁ : Set G)) (hBT₁' : (⁅B, T₁⁆ : Subgroup G) = T₁)
    (himg : IsElemAbelian 2 (imageMod 3 J₁ T₁) ∧ Nat.card (imageMod 3 J₁ T₁) = 4) :
    J ⊓ GLAPPrimeCoreOf 3 L = GLAPPrimeCoreOf 3 J ∧
      ∃ P : Subgroup G, P ≤ J ∧ GLAPPrimeCoreOf 3 J ≤ P ∧ B ≤ Subgroup.normalizer (P : Set G) ∧
        Nat.Coprime 3 (Nat.card P) ∧ Nat.card P = 4 * Nat.card (GLAPPrimeCoreOf 3 J) ∧
        ¬ (⁅B, P⁆ : Subgroup G) ≤ GLAPPrimeCoreOf 3 J := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set Q := GLAPPrimeCoreOf 3 L with hQ
  set Q₁ := GLAPPrimeCoreOf 3 J₁ with hQ₁
  set QJ := GLAPPrimeCoreOf 3 J with hQJ
  have hJL : J ≤ L := hJJ₁.trans hJ₁L
  have hJNQ : J ≤ Subgroup.normalizer (Q : Set G) := hJL.trans (le_normalizer_glaPPrimeCoreOf 3 L)
  have hJ₁NQ₁ : J₁ ≤ Subgroup.normalizer (Q₁ : Set G) := le_normalizer_glaPPrimeCoreOf 3 J₁
  have hJNQ₁ : J ≤ Subgroup.normalizer (Q₁ : Set G) := hJJ₁.trans hJ₁NQ₁
  have hJNQJ : J ≤ Subgroup.normalizer (QJ : Set G) := le_normalizer_glaPPrimeCoreOf 3 J
  have hBQ₁ : B ≤ Subgroup.normalizer (Q₁ : Set G) := fun b hb =>
    normalizer_le_normalizer_glaPPrimeCoreOf 3 J₁ (hBJ₁ hb)
  have hQ₁J₁ : Q₁ ≤ J₁ := Subgroup.map_subtype_le _
  have hQJJ : QJ ≤ J := Subgroup.map_subtype_le _
  have hQ₁ndvd : ¬ 3 ∣ Nat.card Q₁ := not_dvd_card_glaPPrimeCoreOf hp3 J₁
  have hQJndvd : ¬ 3 ∣ Nat.card QJ := not_dvd_card_glaPPrimeCoreOf hp3 J
  have hJ₁Q : J₁ ⊓ Q ≤ Q₁ := inf_glaPPrimeCoreOf_le hp3 hJ₁L
  have hJQ : J ⊓ Q ≤ QJ := inf_glaPPrimeCoreOf_le hp3 hJL
  have hJ₁sup : J₁ ≤ J ⊔ Q₁ := by
    intro g hg
    have hg' : g ∈ (J : Set G) * (Q : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right J Q hJNQ]
      exact hcov hg
    obtain ⟨j, hj, q, hq, rfl⟩ := hg'
    have hqJ₁ : q ∈ J₁ := by
      have e : q = j⁻¹ * (j * q) := by group
      rw [e]
      exact J₁.mul_mem (J₁.inv_mem (hJJ₁ hj)) hg
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hj)
      (Subgroup.mem_sup_right (hJ₁Q ⟨hqJ₁, hq⟩))
  have hQJQ₁ : QJ ≤ Q₁ := by
    set M : Subgroup G := Q₁ ⊔ QJ with hM
    have hMJ₁ : M ≤ J₁ := sup_le hQ₁J₁ (hQJJ.trans hJJ₁)
    have hJM : J ≤ Subgroup.normalizer (M : Set G) := le_normalizer_sup hJNQ₁ hJNQJ
    have hQ₁M : Q₁ ≤ Subgroup.normalizer (M : Set G) := by
      rw [Subgroup.le_normalizer_iff_commutator_le_right]
      have hc : (⁅Q₁, M⁆ : Subgroup G) ≤ Q₁ :=
        Subgroup.le_normalizer_iff_commutator_le_left.1 (hMJ₁.trans hJ₁NQ₁)
      exact hc.trans le_sup_left
    have hJ₁M : J₁ ≤ Subgroup.normalizer (M : Set G) := hJ₁sup.trans (sup_le hJM hQ₁M)
    have hcardM : ¬ 3 ∣ Nat.card M := by
      have h1 := card_sup_mul_card_inf_of_le_normalizer (A := Q₁) (B := QJ)
        (hQJJ.trans hJNQ₁)
      intro hd
      have hd' : 3 ∣ Nat.card Q₁ * Nat.card QJ := by
        rw [← h1]
        exact hd.mul_right _
      rcases (Nat.Prime.dvd_mul hp3).1 hd' with h | h
      exacts [hQ₁ndvd h, hQJndvd h]
    exact le_sup_right.trans (hat_le_glaPPrimeCoreOf hp3 hMJ₁ hJ₁M hcardM)
  have hcap : J ⊓ Q = QJ := le_antisymm hJQ (le_inf hQJJ (hQJQ₁.trans hO₁))
  refine ⟨hcap, ?_⟩
  set P : Subgroup G := J ⊓ (T₁ ⊔ Q₁) with hP
  have hPJ : P ≤ J := inf_le_left
  have hQJP : QJ ≤ P := le_inf hQJJ (hQJQ₁.trans le_sup_right)
  have hBP : B ≤ Subgroup.normalizer (P : Set G) :=
    le_normalizer_inf hBJ (le_normalizer_sup hBT₁ hBQ₁)
  have hPNQ₁ : P ≤ Subgroup.normalizer (Q₁ : Set G) := hPJ.trans hJNQ₁
  have hT₁P : T₁ ≤ P ⊔ Q₁ := by
    intro t ht
    have ht' : t ∈ (J : Set G) * (Q₁ : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right J Q₁ hJNQ₁]
      exact hJ₁sup (hT₁J ht)
    obtain ⟨j, hj, q, hq, rfl⟩ := ht'
    have hjP : j ∈ P := by
      refine ⟨hj, ?_⟩
      have e : j = (j * q) * q⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ht)
        (Subgroup.inv_mem _ (Subgroup.mem_sup_right hq))
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hjP) (Subgroup.mem_sup_right hq)
  have hPsup : P ⊔ Q₁ = T₁ ⊔ Q₁ :=
    le_antisymm (sup_le inf_le_right le_sup_right) (sup_le hT₁P le_sup_right)
  have hQ₁P : Q₁ ⊓ P = QJ := by
    refine le_antisymm ?_ (le_inf hQJQ₁ hQJP)
    intro x hx
    rw [← hcap]
    exact ⟨hPJ hx.2, hO₁ hx.1⟩
  have hT₁N : T₁ ≤ Subgroup.normalizer (Q₁ : Set G) := hT₁J.trans hJ₁NQ₁
  have hQ₁sub : Q₁.subgroupOf J₁ = GLAPPrimeCore 3 ↥J₁ :=
    Subgroup.comap_map_eq_self_of_injective J₁.subtype_injective _
  have hkey : Nat.card (imageMod 3 J₁ T₁) * Nat.card (Q₁ ⊓ T₁ : Subgroup G) = Nat.card T₁ := by
    unfold imageMod
    rw [← Subgroup.relIndex_ker (T₁.subgroupOf J₁) (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J₁)),
      QuotientGroup.ker_mk']
    have h1 := Subgroup.relIndex_mul_card (H := GLAPPrimeCore 3 ↥J₁) (K := T₁.subgroupOf J₁)
    have h2 : GLAPPrimeCore 3 ↥J₁ ⊓ T₁.subgroupOf J₁ = (Q₁ ⊓ T₁).subgroupOf J₁ := by
      rw [← hQ₁sub]
      exact (Subgroup.comap_inf _ _ _).symm
    rw [h2] at h1
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hT₁J : Q₁ ⊓ T₁ ≤ J₁)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₁J).toEquiv] at h1
    exact h1
  rw [himg.2] at hkey
  have hposQ₁T₁ : 0 < Nat.card (Q₁ ⊓ T₁ : Subgroup G) := Nat.card_pos
  have hposQ₁ : 0 < Nat.card Q₁ := Nat.card_pos
  have hsupT : Nat.card (Q₁ ⊔ T₁ : Subgroup G) = 4 * Nat.card Q₁ := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer hT₁N
    rw [← hkey] at h1
    have h2 : Nat.card (Q₁ ⊔ T₁ : Subgroup G) * Nat.card (Q₁ ⊓ T₁ : Subgroup G) =
        (4 * Nat.card Q₁) * Nat.card (Q₁ ⊓ T₁ : Subgroup G) := by
      rw [h1]
      ring
    exact Nat.eq_of_mul_eq_mul_right hposQ₁T₁ h2
  have hPcard : Nat.card P = 4 * Nat.card QJ := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer hPNQ₁
    have hsupP : Q₁ ⊔ P = Q₁ ⊔ T₁ := by
      rw [sup_comm Q₁ P, hPsup, sup_comm]
    rw [hsupP, hsupT, hQ₁P] at h1
    have h2 : Nat.card Q₁ * (4 * Nat.card QJ) = Nat.card Q₁ * Nat.card P := by
      rw [← h1]
      ring
    exact (Nat.eq_of_mul_eq_mul_left hposQ₁ h2).symm
  refine ⟨P, hPJ, hQJP, hBP, ?_, hPcard, ?_⟩
  · rw [hPcard]
    exact Nat.Coprime.mul_right (by norm_num) ((Nat.Prime.coprime_iff_not_dvd hp3).2 hQJndvd)
  · intro hle
    have hT₁Q₁ : T₁ ≤ Q₁ := by
      calc T₁ = ⁅B, T₁⁆ := hBT₁'.symm
        _ ≤ Q₁ := by
          refine Subgroup.commutator_le.2 fun b hb t ht => ?_
          have ht' : t ∈ (P : Set G) * (Q₁ : Set G) := by
            rw [← Subgroup.coe_mul_of_left_le_normalizer_right P Q₁ hPNQ₁]
            exact hT₁P ht
          obtain ⟨p', hp', q, hq, rfl⟩ := ht'
          have e : ⁅b, p' * q⁆ = ⁅b, p'⁆ * (p' * ⁅b, q⁆ * p'⁻¹) := by
            simp only [commutatorElement_def]
            group
          rw [e]
          refine Q₁.mul_mem (hQJQ₁ (hle (Subgroup.commutator_mem_commutator hb hp'))) ?_
          have hbq : ⁅b, q⁆ ∈ Q₁ := by
            have e2 : ⁅b, q⁆ = (b * q * b⁻¹) * q⁻¹ := by
              simp only [commutatorElement_def]
            rw [e2]
            exact Q₁.mul_mem ((Subgroup.mem_normalizer_iff.1 (hBQ₁ hb) q).1 hq) (Q₁.inv_mem hq)
          have := (Subgroup.mem_normalizer_iff.1 (hPNQ₁ hp') _).1 hbq
          simpa [mul_assoc] using this
    rw [inf_eq_right.2 hT₁Q₁] at hkey
    have hpos : 0 < Nat.card T₁ := Nat.card_pos
    omega

theorem exists_T_of_P {B A L J P Rs : Subgroup G} (hBel : IsElemAbelian 3 B) (hAB : A ≤ B)
    (hRsO : Rs ≤ GLAPPrimeCoreOf 3 L) (hRs2 : IsPGroup 2 Rs)
    (hRsidx : ¬ 2 ∣ Rs.relIndex (GLAPPrimeCoreOf 3 L)) (hBRs : B ≤ Subgroup.normalizer (Rs : Set G))
    (hJR : J ≤ Subgroup.normalizer (Rs : Set G)) (hJA : J ≤ Subgroup.centralizer (A : Set G))
    (hBJ : B ≤ Subgroup.normalizer (J : Set G))
    (hJcapQ : J ⊓ GLAPPrimeCoreOf 3 L = GLAPPrimeCoreOf 3 J) (hPJ : P ≤ J)
    (hOP : GLAPPrimeCoreOf 3 J ≤ P) (hBP : B ≤ Subgroup.normalizer (P : Set G))
    (hP3 : Nat.Coprime 3 (Nat.card P)) (hPc : Nat.card P = 4 * Nat.card (GLAPPrimeCoreOf 3 J))
    (hPnc : ¬ (⁅B, P⁆ : Subgroup G) ≤ GLAPPrimeCoreOf 3 J) :
    ∃ T : Subgroup G, T ≤ J ⊔ Rs ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧ Rs ≤ T ∧
      (Rs.subgroupOf T).Normal ∧ Nat.card T = 4 * Nat.card Rs ∧
      (∀ a ∈ A, ∀ t ∈ T, ⁅a, t⁆ ∈ Rs) ∧ ¬ (⁅B, T⁆ : Subgroup G) ≤ Rs ∧
      T ⊓ (GLAPPrimeCoreOf 3 J ⊔ Rs) ≤ Rs := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set Q := GLAPPrimeCoreOf 3 L with hQ
  set QJ := GLAPPrimeCoreOf 3 J with hQJ
  have hQJJ : QJ ≤ J := Subgroup.map_subtype_le _
  have hQJQ : QJ ≤ Q := hJcapQ.symm.le.trans inf_le_right
  have hBQJ : B ≤ Subgroup.normalizer (QJ : Set G) := fun b hb =>
    normalizer_le_normalizer_glaPPrimeCoreOf 3 J (hBJ hb)
  have hPN : P ≤ Subgroup.normalizer (QJ : Set G) :=
    hPJ.trans (le_normalizer_glaPPrimeCoreOf 3 J)
  obtain ⟨TJ, -, hTJP, hTJ2, hTJodd, hBTJ⟩ := exists_invariant_sylow_ge hp3 (by norm_num)
    (X := P) (R := ⊥) (isPGroup_of_isElemAbelian hBel) hBP hP3 bot_le
    (IsPGroup.of_card (by simp : Nat.card (⊥ : Subgroup G) = 2 ^ 0))
    (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top)
  have hQJrel : QJ.relIndex P = 4 := by
    have h1 := Subgroup.relIndex_mul_card (H := QJ) (K := P)
    rw [inf_eq_left.2 hOP, hPc] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hPsup : P ≤ TJ ⊔ QJ := by
    have hd1 : (TJ ⊔ QJ).relIndex P ∣ QJ.relIndex P :=
      Subgroup.relIndex_dvd_of_le_left P (le_sup_right : QJ ≤ TJ ⊔ QJ)
    have hd2 : (TJ ⊔ QJ).relIndex P ∣ TJ.relIndex P :=
      Subgroup.relIndex_dvd_of_le_left P (le_sup_left : TJ ≤ TJ ⊔ QJ)
    rw [hQJrel] at hd1
    have hd : (TJ ⊔ QJ).relIndex P = 1 := by
      have hmem : (TJ ⊔ QJ).relIndex P ∈ Nat.divisors 4 := Nat.mem_divisors.2 ⟨hd1, by norm_num⟩
      have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
      rw [hdiv] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h
      · exact h
      · rw [h] at hd2
        exact absurd hd2 hTJodd
      · rw [h] at hd2
        exact absurd ((by norm_num : 2 ∣ 4).trans hd2) hTJodd
    exact Subgroup.relIndex_eq_one.1 hd
  have hPeq : QJ ⊔ TJ = P := by
    rw [sup_comm]
    exact le_antisymm (sup_le hTJP hOP) hPsup
  set H : Subgroup G := QJ ⊔ Rs with hH
  have hRsH : Rs ≤ H := le_sup_right
  have hHQ : H ≤ Q := sup_le hQJQ hRsO
  have hHN : H ≤ Subgroup.normalizer (Rs : Set G) :=
    sup_le (hQJJ.trans hJR) Subgroup.le_normalizer
  have hRsHodd : ¬ 2 ∣ Rs.relIndex H := by
    intro hd
    apply hRsidx
    rw [← Subgroup.relIndex_mul_relIndex Rs H Q hRsH hHQ]
    exact hd.mul_right _
  have hH2 : ∀ X : Subgroup G, X ≤ H → IsPGroup 2 X → X ≤ Rs := fun X hXH hX2 =>
    hat_le_of_isPGroup_two hRsH hHN hRs2 hRsHodd hXH hX2
  have hTJRs : TJ ⊓ Rs = TJ ⊓ QJ := by
    refine le_antisymm (le_inf inf_le_left ?_) ?_
    · intro x hx
      rw [← hJcapQ]
      exact ⟨hPJ (hTJP hx.1), hRsO hx.2⟩
    · exact le_inf inf_le_left
        (hH2 (TJ ⊓ QJ) (inf_le_right.trans le_sup_left) (hTJ2.to_le inf_le_left))
  have hTJN : TJ ≤ Subgroup.normalizer (Rs : Set G) := hTJP.trans (hPJ.trans hJR)
  have hT2 : IsPGroup 2 (TJ ⊔ Rs : Subgroup G) := hTJ2.to_sup_of_normal_right' hRs2 hTJN
  have hTN : (TJ ⊔ Rs) ≤ Subgroup.normalizer (Rs : Set G) :=
    sup_le hTJN Subgroup.le_normalizer
  have hBT : B ≤ Subgroup.normalizer ((TJ ⊔ Rs : Subgroup G) : Set G) :=
    le_normalizer_sup hBTJ hBRs
  have hTJcard : Nat.card TJ = 4 * Nat.card (TJ ⊓ QJ : Subgroup G) := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer (A := QJ) (B := TJ) (hTJP.trans hPN)
    rw [hPeq, hPc, inf_comm] at h1
    have h2 : Nat.card QJ * (4 * Nat.card (TJ ⊓ QJ : Subgroup G)) =
        Nat.card QJ * Nat.card TJ := by
      rw [← h1]
      ring
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h2).symm
  have hTcard : Nat.card (TJ ⊔ Rs : Subgroup G) = 4 * Nat.card Rs := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer (A := Rs) (B := TJ) hTJN
    rw [sup_comm Rs TJ, inf_comm Rs TJ, hTJRs, hTJcard] at h1
    have h2 : Nat.card (TJ ⊔ Rs : Subgroup G) * Nat.card (TJ ⊓ QJ : Subgroup G) =
        (4 * Nat.card Rs) * Nat.card (TJ ⊓ QJ : Subgroup G) := by
      rw [h1]
      ring
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hAT : ∀ a ∈ A, ∀ t ∈ (TJ ⊔ Rs : Subgroup G), ⁅a, t⁆ ∈ Rs := by
    intro a ha t ht
    have ht' : t ∈ (TJ : Set G) * (Rs : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right TJ Rs hTJN]
      exact ht
    obtain ⟨x, hx, r, hr, rfl⟩ := ht'
    have hxJ : x ∈ J := hPJ (hTJP hx)
    have hxA : a * x = x * a := Subgroup.mem_centralizer_iff.1 (hJA hxJ) a ha
    have e : ⁅a, x * r⁆ = ⁅a, x⁆ * (x * ⁅a, r⁆ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e, commutatorElement_eq_one_iff_mul_comm.2 hxA, one_mul]
    have har : ⁅a, r⁆ ∈ Rs := by
      have e2 : ⁅a, r⁆ = (a * r * a⁻¹) * r⁻¹ := by simp only [commutatorElement_def]
      rw [e2]
      exact Rs.mul_mem ((Subgroup.mem_normalizer_iff.1 (hBRs (hAB ha)) r).1 hr) (Rs.inv_mem hr)
    exact (Subgroup.mem_normalizer_iff.1 (hJR hxJ) _).1 har |> fun h => by simpa using h
  have hBTnc : ¬ (⁅B, TJ ⊔ Rs⁆ : Subgroup G) ≤ Rs := by
    intro hle
    apply hPnc
    refine Subgroup.commutator_le.2 fun b hb p hp => ?_
    have hp' : p ∈ (TJ : Set G) * (QJ : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right TJ QJ (hTJP.trans hPN)]
      exact hPsup hp
    obtain ⟨x, hx, q, hq, rfl⟩ := hp'
    have e : ⁅b, x * q⁆ = ⁅b, x⁆ * (x * ⁅b, q⁆ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have hbx : ⁅b, x⁆ ∈ TJ ⊓ Rs := by
      refine ⟨?_, hle (Subgroup.commutator_mem_commutator hb (Subgroup.mem_sup_left hx))⟩
      have e2 : ⁅b, x⁆ = (b * x * b⁻¹) * x⁻¹ := by simp only [commutatorElement_def]
      rw [e2]
      exact TJ.mul_mem ((Subgroup.mem_normalizer_iff.1 (hBTJ hb) x).1 hx) (TJ.inv_mem hx)
    have hbx' : ⁅b, x⁆ ∈ TJ ⊓ QJ := by
      rw [← hTJRs]
      exact hbx
    have hbq : ⁅b, q⁆ ∈ QJ := by
      have e3 : ⁅b, q⁆ = (b * q * b⁻¹) * q⁻¹ := by simp only [commutatorElement_def]
      rw [e3]
      exact QJ.mul_mem ((Subgroup.mem_normalizer_iff.1 (hBQJ hb) q).1 hq) (QJ.inv_mem hq)
    have hxN : x ∈ Subgroup.normalizer (QJ : Set G) := hTJP.trans hPN hx
    refine QJ.mul_mem hbx'.2 ?_
    have := (Subgroup.mem_normalizer_iff.1 hxN _).1 hbq
    simpa [mul_assoc] using this
  refine ⟨TJ ⊔ Rs, sup_le_sup_right (hTJP.trans hPJ) Rs, hT2, hBT, le_sup_right, ?_, hTcard,
    hAT, hBTnc, ?_⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2 hTN
  · exact hH2 _ inf_le_right (hT2.to_le inf_le_left)

theorem exists_T_data {B A L J₁ T₁ Rs J : Subgroup G} (hBel : IsElemAbelian 3 B) (hAB : A ≤ B)
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) (hRsO : Rs ≤ GLAPPrimeCoreOf 3 L)
    (hRs2 : IsPGroup 2 Rs) (hRsidx : ¬ 2 ∣ Rs.relIndex (GLAPPrimeCoreOf 3 L))
    (hBRs : B ≤ Subgroup.normalizer (Rs : Set G)) (hJL : J ≤ L)
    (hJR : J ≤ Subgroup.normalizer (Rs : Set G)) (hJA : J ≤ Subgroup.centralizer (A : Set G))
    (hBJ : B ≤ Subgroup.normalizer (J : Set G)) (hJlay : GLAPLayer 3 J = J) (hJJ₁ : J ≤ J₁)
    (hJ₁L : J₁ ≤ L) (hBJ₁ : B ≤ Subgroup.normalizer (J₁ : Set G))
    (hcov : J₁ ≤ J ⊔ GLAPPrimeCoreOf 3 L) (hO₁ : GLAPPrimeCoreOf 3 J₁ ≤ GLAPPrimeCoreOf 3 L)
    (hT₁J : T₁ ≤ J₁) (hT₁2 : IsPGroup 2 T₁)
    (hBT₁ : B ≤ Subgroup.normalizer (T₁ : Set G)) (hBT₁' : (⁅B, T₁⁆ : Subgroup G) = T₁)
    (himg : IsElemAbelian 2 (imageMod 3 J₁ T₁) ∧ Nat.card (imageMod 3 J₁ T₁) = 4) :
    ∃ T : Subgroup G, T ≤ J ⊔ Rs ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧ Rs ≤ T ∧
      (Rs.subgroupOf T).Normal ∧ Nat.card T = 4 * Nat.card Rs ∧
      (∀ a ∈ A, ∀ t ∈ T, ⁅a, t⁆ ∈ Rs) ∧ ¬ (⁅B, T⁆ : Subgroup G) ≤ Rs ∧
      T ⊓ (GLAPPrimeCoreOf 3 J ⊔ Rs) ≤ Rs := by
  obtain ⟨hcap, P, hPJ, hOP, hBP, hP3, hPc, hPnc⟩ :=
    exists_P_data hBel hBJ hJJ₁ hJ₁L hBJ₁ hcov hO₁ hT₁J hT₁2 hBT₁ hBT₁' himg
  exact exists_T_of_P hBel hAB hRsO hRs2 hRsidx hBRs hJR hJA hBJ hcap hPJ hOP hBP hP3 hPc hPnc

theorem normal_hatN {B A T Rs J : Subgroup G} (hRT : Rs ≤ T) (hRn : (Rs.subgroupOf T).Normal)
    (hTJ : T ≤ J ⊔ Rs) (hJR : J ≤ Subgroup.normalizer (Rs : Set G))
    (hJA : J ≤ Subgroup.centralizer (A : Set G))
    (hJC : (⁅Rs ⊓ Subgroup.centralizer (A : Set G), J⁆ : Subgroup G) = ⊥)
    (hBT : B ≤ Subgroup.normalizer (T : Set G)) (hBR : B ≤ Subgroup.normalizer (Rs : Set G))
    (hAB : A ≤ B) (hBel : IsElemAbelian 3 B) :
    ((hatN Rs A).subgroupOf T).Normal ∧ B ≤ Subgroup.normalizer (hatN Rs A : Set G) := by
  have hBC : B ≤ Subgroup.centralizer (A : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact isElemAbelian_commute hBel (hAB ha) hg
  have hNle : hatN Rs A ≤ T := (hatN_le Rs A).trans hRT
  have hJN : J ≤ Subgroup.normalizer (hatN Rs A : Set G) :=
    le_normalizer_sup (le_normalizer_frat2 hJR)
      (le_normalizer_inf hJR (hJA.trans Subgroup.le_normalizer))
  have hRN : Rs ≤ Subgroup.normalizer (hatN Rs A : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    exact (Subgroup.commutator_mono le_rfl (hatN_le Rs A)).trans
      ((commutator_le_frat2 Rs).trans (frat2_le_hatN Rs A))
  have hTN : T ≤ Subgroup.normalizer (hatN Rs A : Set G) := hTJ.trans (sup_le hJN hRN)
  refine ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer hNle).2 hTN, ?_⟩
  exact le_normalizer_sup (le_normalizer_frat2 hBR)
    (le_normalizer_inf hBR (hBC.trans Subgroup.le_normalizer))

private theorem hat_comm_identity {j r a c u : G} (hja : j * a = a * j) (hc : ⁅j, r⁆ = c)
    (hu : ⁅r, a⁆ = u) :
    ⁅j, u⁆ = ⁅c, u⁆ * ((u * c) * ⁅a, c⁻¹⁆ * (u * c)⁻¹) := by
  have e1 : j * a * j⁻¹ = a := by
    rw [hja]
    group
  have e2 : j * a⁻¹ * j⁻¹ = a⁻¹ :=
    calc j * a⁻¹ * j⁻¹ = (j * a * j⁻¹)⁻¹ := by group
      _ = a⁻¹ := by rw [e1]
  have key : j * u * j⁻¹ = (j * r * j⁻¹) * a * (j * r⁻¹ * j⁻¹) * a⁻¹ := by
    calc j * u * j⁻¹
        = (j * r * j⁻¹) * (j * a * j⁻¹) * (j * r⁻¹ * j⁻¹) * (j * a⁻¹ * j⁻¹) := by
          rw [← hu]
          simp only [commutatorElement_def]
          group
      _ = (j * r * j⁻¹) * a * (j * r⁻¹ * j⁻¹) * a⁻¹ := by rw [e1, e2]
  have h4 : ⁅j, u⁆ = (j * r * j⁻¹) * a * (j * r⁻¹ * j⁻¹) * a⁻¹ * u⁻¹ := by
    rw [commutatorElement_def, key]
  rw [h4]
  subst hc hu
  simp only [commutatorElement_def]
  group

theorem trivial_on_frat {A J Rs : Subgroup G} (hRs2 : IsPGroup 2 Rs) (hAel : IsElemAbelian 3 A)
    (hAR : A ≤ Subgroup.normalizer (Rs : Set G)) (hJR : J ≤ Subgroup.normalizer (Rs : Set G))
    (hJA : J ≤ Subgroup.centralizer (A : Set G))
    (hJC : (⁅Rs ⊓ Subgroup.centralizer (A : Set G), J⁆ : Subgroup G) = ⊥) {j : G} (hj : j ∈ J)
    (h : ∀ r ∈ Rs, ⁅j, r⁆ ∈ hatN Rs A) : ∀ r ∈ Rs, ⁅j, r⁆ ∈ frat2 Rs := by
  have hΦR : frat2 Rs ≤ Rs := (frat2_le_hatN Rs A).trans (hatN_le Rs A)
  have hRΦ : Rs ≤ Subgroup.normalizer (frat2 Rs : Set G) :=
    le_normalizer_frat2 Subgroup.le_normalizer
  have hAΦ : A ≤ Subgroup.normalizer (frat2 Rs : Set G) := le_normalizer_frat2 hAR
  have hNZ : hatN Rs A ≤ hatModComm Rs (frat2 Rs) (A : Set G) hRΦ := by
    refine sup_le ?_ ?_
    · intro n hn
      refine ⟨hΦR hn, fun a ha => ?_⟩
      have e : ⁅n, a⁆ = n * (a * n⁻¹ * a⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (frat2 Rs).mul_mem hn
        ((Subgroup.mem_normalizer_iff.1 (hAΦ ha) n⁻¹).1 ((frat2 Rs).inv_mem hn))
    · rintro n ⟨hnR, hnC⟩
      refine ⟨hnR, fun a ha => ?_⟩
      have hc : a * n = n * a := Subgroup.mem_centralizer_iff.1 hnC a ha
      rw [commutatorElement_eq_one_iff_mul_comm.2 hc.symm]
      exact (frat2 Rs).one_mem
  set Q := hatModComm Rs (frat2 Rs) ({j} : Set G) hRΦ with hQ
  have hCQ : Rs ⊓ Subgroup.centralizer (A : Set G) ≤ Q := by
    intro x hx
    refine ⟨hx.1, fun y hy => ?_⟩
    rw [Set.mem_singleton_iff.1 hy]
    have hxj : ⁅x, j⁆ ∈ (⁅Rs ⊓ Subgroup.centralizer (A : Set G), J⁆ : Subgroup G) :=
      Subgroup.commutator_mem_commutator hx hj
    rw [hJC, Subgroup.mem_bot] at hxj
    rw [hxj]
    exact (frat2 Rs).one_mem
  have hRAQ : (⁅Rs, A⁆ : Subgroup G) ≤ Q := by
    refine Subgroup.commutator_le.2 fun r hr a ha => ?_
    have hu : ⁅r, a⁆ ∈ Rs := by
      have e : ⁅r, a⁆ = r * (a * r⁻¹ * a⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Rs.mul_mem hr ((Subgroup.mem_normalizer_iff.1 (hAR ha) r⁻¹).1 (Rs.inv_mem hr))
    refine ⟨hu, fun y hy => ?_⟩
    rw [Set.mem_singleton_iff.1 hy]
    have hcN : ⁅j, r⁆ ∈ hatN Rs A := h r hr
    have hcR : ⁅j, r⁆ ∈ Rs := hatN_le Rs A hcN
    have hja : j * a = a * j := (Subgroup.mem_centralizer_iff.1 (hJA hj) a ha).symm
    have hφ : ⁅a, ⁅j, r⁆⁻¹⁆ ∈ frat2 Rs := by
      have h1 := (hNZ ((hatN Rs A).inv_mem hcN)).2 a ha
      rw [← commutatorElement_inv]
      exact (frat2 Rs).inv_mem h1
    have hX : ⁅j, ⁅r, a⁆⁆ ∈ frat2 Rs := by
      rw [hat_comm_identity hja rfl rfl]
      exact (frat2 Rs).mul_mem
        (commutator_le_frat2 Rs (Subgroup.commutator_mem_commutator hcR hu))
        ((Subgroup.mem_normalizer_iff.1 (hRΦ (Rs.mul_mem hu hcR)) _).1 hφ)
    rw [← commutatorElement_inv]
    exact (frat2 Rs).inv_mem hX
  have hRsQ : Rs ≤ Q := by
    have hfac := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
      3 Nat.prime_three A Rs (isPGroup_of_isElemAbelian hAel) (hat_not_dvd_three hRs2) hAR
    calc Rs = ⁅Rs, A⁆ ⊔ (Rs ⊓ Subgroup.centralizer (A : Set G)) := hfac
      _ ≤ Q := sup_le hRAQ hCQ
  intro r hr
  have h1 := (hRsQ hr).2 j rfl
  rw [← commutatorElement_inv]
  exact (frat2 Rs).inv_mem h1

theorem burnside_frat {Rs : Subgroup G} {k : G} (hRs2 : IsPGroup 2 Rs)
    (hk : k ∈ Subgroup.normalizer (Rs : Set G)) (h : ∀ r ∈ Rs, ⁅k, r⁆ ∈ frat2 Rs) :
    ∃ n : ℕ, k ^ (2 ^ n) ∈ Subgroup.centralizer (Rs : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 ↥Rs) := ⟨hRs2⟩
  have hfr : ∀ x : ↥Rs, (x : G) ∈ frat2 Rs → x ∈ frattini ↥Rs := by
    have hle : frat2 Rs ≤ (frattini ↥Rs).map Rs.subtype := by
      refine sup_le ?_ ?_
      · rw [Subgroup.commutator_le]
        intro a ha b hb
        refine ⟨⁅(⟨a, ha⟩ : ↥Rs), ⟨b, hb⟩⁆, ?_, rfl⟩
        exact CFSG.commutator_le_frattini_of_isPGroup (p := 2)
          (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
      · rw [Subgroup.closure_le]
        rintro g ⟨r, hr, rfl⟩
        exact ⟨(⟨r, hr⟩ : ↥Rs) ^ 2, CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) _, rfl⟩
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hle hx
    have hyx : y = x := Subtype.ext hxy
    rwa [hyx] at hy
  let g : ↥(Subgroup.normalizer (Rs : Set G)) := ⟨k, hk⟩
  have hmem : (Rs.normalizerMonoidHom g : MulAut ↥Rs) ∈
      (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥Rs)).ker := by
    rw [CFSG.OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel]
    intro r
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    apply hfr
    have e : (((Rs.normalizerMonoidHom g r)⁻¹ * r : ↥Rs) : G) = ⁅k, (r : G)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      show (k * (r : G) * k⁻¹)⁻¹ * (r : G) = _
      group
    rw [e]
    exact h _ (Rs.inv_mem r.2)
  obtain ⟨n, hn⟩ := CFSG.OrderReductions.FrattiniAutomorphisms.frattini_automorphism_kernel_isPGroup 2
    hRs2 ⟨Rs.normalizerMonoidHom g, hmem⟩
  have hn' : Rs.normalizerMonoidHom (g ^ 2 ^ n) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hn
  refine ⟨n, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have h1 := congrArg (fun f : MulAut ↥Rs => ((f ⟨q, hq⟩ : ↥Rs) : G)) hn'
  have h2 : (((g ^ 2 ^ n : ↥(Subgroup.normalizer (Rs : Set G))) : G)) * q *
      (((g ^ 2 ^ n : ↥(Subgroup.normalizer (Rs : Set G))) : G))⁻¹ = q := h1
  rw [Subgroup.coe_pow] at h2
  calc q * k ^ 2 ^ n = (k ^ 2 ^ n * q * (k ^ 2 ^ n)⁻¹) * k ^ 2 ^ n := by rw [h2]
    _ = k ^ 2 ^ n * q := by group

theorem oPPrimeP_pow_mem (p : ℕ) (X : Subgroup G) {q : G} (hq : q ∈ oPPrimeP p X) :
    ∃ n : ℕ, q ^ (p ^ n) ∈ GLAPPrimeCoreOf p X := by
  unfold oPPrimeP at hq
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hq
  rw [Subgroup.mem_comap] at hm
  obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (⟨_, hm⟩ : ↥(CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X)))
  refine ⟨n, ?_⟩
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) (m ^ (p ^ n)) = 1 := by
    rw [map_pow]
    have := congrArg Subtype.val hn
    simpa using this
  unfold GLAPPrimeCoreOf
  refine Subgroup.mem_map.2 ⟨m ^ (p ^ n), (QuotientGroup.eq_one_iff _).1 h1, ?_⟩
  simp

private theorem hat_le_normalizer_oPPrimeP (p : ℕ) (X : Subgroup G) :
    X ≤ Subgroup.normalizer (oPPrimeP p X : Set G) := by
  have key : ∀ {x h : G}, x ∈ X → h ∈ oPPrimeP p X → x * h * x⁻¹ ∈ oPPrimeP p X := by
    intro x h hx hh
    unfold oPPrimeP at hh ⊢
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hh
    refine Subgroup.mem_map.2 ⟨(⟨x, hx⟩ : ↥X) * m * (⟨x, hx⟩ : ↥X)⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_comap] at hm ⊢
      rw [map_mul, map_mul, map_inv]
      haveI : (CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X)).Normal := CFSG.pCore_normal
      exact Subgroup.Normal.conj_mem inferInstance _ hm _
    · simp
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key hx hh, fun hh => ?_⟩
  have := key (X.inv_mem hx) hh
  simpa [mul_assoc] using this

private theorem hat_mem_glaPPrimeCoreOf {p : ℕ} {A : Subgroup G} (a : ↥A) :
    (a : G) ∈ GLAPPrimeCoreOf p A ↔ a ∈ GLAPPrimeCore p ↥A := by
  unfold GLAPPrimeCoreOf
  constructor
  · intro h
    obtain ⟨a', ha', hv⟩ := Subgroup.mem_map.1 h
    have : a' = a := Subtype.ext hv
    rwa [this] at ha'
  · intro h
    exact Subgroup.mem_map.2 ⟨a, h, rfl⟩

theorem inf_oPPrimeP_le {p : ℕ} (hp : p.Prime) {J L : Subgroup G} (hJL : J ≤ L) :
    J ⊓ oPPrimeP p L ≤ oPPrimeP p J := by
  intro x hx
  have hJn : J ≤ Subgroup.normalizer ((J ⊓ oPPrimeP p L : Subgroup G) : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer (hJL.trans (hat_le_normalizer_oPPrimeP p L))
  have hKn : ((J ⊓ oPPrimeP p L).subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 hJn
  have hKbn : (((J ⊓ oPPrimeP p L).subgroupOf J).map
      (QuotientGroup.mk' (GLAPPrimeCore p ↥J))).Normal :=
    hKn.map _ (QuotientGroup.mk'_surjective _)
  have hKbp : IsPGroup p (((J ⊓ oPPrimeP p L).subgroupOf J).map
      (QuotientGroup.mk' (GLAPPrimeCore p ↥J))) := by
    rintro ⟨_, y, hy, rfl⟩
    obtain ⟨n, hn⟩ := oPPrimeP_pow_mem p L (Subgroup.mem_subgroupOf.1 hy).2
    refine ⟨n, Subtype.ext ?_⟩
    have h1 : (y ^ (p ^ n) : ↥J) ∈ GLAPPrimeCore p ↥J := by
      rw [← hat_mem_glaPPrimeCoreOf]
      exact inf_glaPPrimeCoreOf_le hp hJL ⟨J.pow_mem y.2 _, hn⟩
    show QuotientGroup.mk' (GLAPPrimeCore p ↥J) y ^ (p ^ n) = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 h1
  have hle : (((J ⊓ oPPrimeP p L).subgroupOf J).map
      (QuotientGroup.mk' (GLAPPrimeCore p ↥J))) ≤ CFSG.pCore p (↥J ⧸ GLAPPrimeCore p ↥J) :=
    le_sSup ⟨hKbn, hKbp⟩
  unfold oPPrimeP
  exact Subgroup.mem_map.2
    ⟨⟨x, hx.1⟩, hle ⟨⟨x, hx.1⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩, rfl⟩

theorem le_oPPrimeP_of_two_power {J K₀ : Subgroup G} (hJlay : GLAPLayer 3 J = J) (hK₀J : K₀ ≤ J)
    (hK₀n : (K₀.subgroupOf J).Normal)
    (h : ∀ j ∈ K₀, ∃ n : ℕ, j ^ (2 ^ n) ∈ oPPrimeP 3 J) : K₀ ≤ oPPrimeP 3 J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hψ : ∀ y : ↥J, (y : G) ∈ oPPrimeP 3 J ↔
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) y ∈ CFSG.pCore 3 (↥J ⧸ GLAPPrimeCore 3 ↥J) := by
    intro y
    unfold oPPrimeP
    constructor
    · rintro ⟨m, hm, hmy⟩
      have : m = y := Subtype.ext hmy
      rw [this] at hm
      exact hm
    · intro hy
      exact ⟨y, hy, rfl⟩
  set Kb : Subgroup (↥J ⧸ GLAPPrimeCore 3 ↥J) :=
    (K₀.subgroupOf J).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) with hKb
  have hKbn : Kb.Normal := hK₀n.map _ (QuotientGroup.mk'_surjective _)
  have hsolv : Group.IsSolvable ↥Kb := by
    set W : Subgroup ↥Kb := (CFSG.pCore 3 (↥J ⧸ GLAPPrimeCore 3 ↥J)).subgroupOf Kb with hW
    haveI hWn : W.Normal := inferInstance
    have hW3 : IsPGroup 3 ↥W := by
      intro w
      obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup
        (⟨((w : ↥Kb) : ↥J ⧸ GLAPPrimeCore 3 ↥J), w.2⟩ :
          ↥(CFSG.pCore 3 (↥J ⧸ GLAPPrimeCore 3 ↥J)))
      refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hn
      simpa using this
    haveI : Group.IsNilpotent ↥W := hW3.isNilpotent
    have hWsolv : Group.IsSolvable ↥W := inferInstance
    have hquot2 : IsPGroup 2 (↥Kb ⧸ W) := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨_, hxK⟩ := x
      obtain ⟨y, hy, rfl⟩ := hxK
      obtain ⟨n, hn⟩ := h (y : G) (Subgroup.mem_subgroupOf.1 hy)
      refine ⟨n, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hW, Subgroup.mem_subgroupOf]
      have := (hψ (y ^ (2 ^ n))).1 (by simpa using hn)
      simpa using this
    haveI : Group.IsNilpotent (↥Kb ⧸ W) := hquot2.isNilpotent
    haveI : Group.IsSolvable (↥Kb ⧸ W) := inferInstance
    exact solvable_of_ker_le_range W.subtype (QuotientGroup.mk' W)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  have hcomm : ∀ Q : Subgroup G, GLAPComponent 3 J Q → ⁅barX 3 J Q, Kb⁆ = ⊥ := by
    intro Q hQ
    haveI := hKbn
    rcases CFSG.ComponentClassification.LocalComponents.normal_contains_or_commutes
        (barX 3 J Q) Kb hQ.2.2.1 with hle | hc
    · exfalso
      haveI : Group.IsPerfect ↥(barX 3 J Q) := Group.isPerfect_def.2 hQ.2.2.1.2.2.1
      haveI : Nontrivial ↥(barX 3 J Q) := isQuasisimple_nontrivial hQ.2.2.1.2.2
      haveI : Group.IsSolvable ↥(barX 3 J Q) :=
        solvable_of_solvable_injective (Subgroup.inclusion_injective hle)
      exact Group.IsPerfect.not_isSolvable _ this
    · exact hc
  intro j hjK
  have hjJ : j ∈ J := hK₀J hjK
  have hjb : QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) (⟨j, hjJ⟩ : ↥J) ∈ Kb :=
    ⟨⟨j, hjJ⟩, Subgroup.mem_subgroupOf.2 hjK, rfl⟩
  set Y : Subgroup G := hatModComm J (GLAPPrimeCoreOf 3 J) ({j} : Set G)
    (le_normalizer_glaPPrimeCoreOf 3 J) with hY
  have hQY : ∀ Q : Subgroup G, GLAPComponent 3 J Q → Q ≤ Y := by
    intro Q hQ q hq
    refine ⟨hQ.1 hq, fun z hz => ?_⟩
    rw [Set.mem_singleton_iff.1 hz]
    have hqb : QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) (⟨q, hQ.1 hq⟩ : ↥J) ∈ barX 3 J Q :=
      ⟨⟨q, hQ.1 hq⟩, Subgroup.mem_subgroupOf.2 hq, rfl⟩
    have h1 := Subgroup.commutator_mem_commutator hqb hjb
    rw [hcomm Q hQ, Subgroup.mem_bot] at h1
    rw [← map_commutatorElement] at h1
    exact (hat_mem_glaPPrimeCoreOf (⁅(⟨q, hQ.1 hq⟩ : ↥J), ⟨j, hjJ⟩⁆)).2 ((QuotientGroup.eq_one_iff _).1 h1)
  have hJY : J ≤ Y := by
    rw [← hJlay]
    exact sSup_le fun Q hQ => hQY Q hQ
  have hcen : ∀ w : ↥J ⧸ GLAPPrimeCore 3 ↥J,
      w * QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) (⟨j, hjJ⟩ : ↥J) =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) (⟨j, hjJ⟩ : ↥J) * w := by
    intro w
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥J) w
    have h1 := (hJY y.2).2 j rfl
    have h2 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) ⁅y, (⟨j, hjJ⟩ : ↥J)⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).2 ((hat_mem_glaPPrimeCoreOf (⁅y, (⟨j, hjJ⟩ : ↥J)⁆)).1 h1)
    rw [map_commutatorElement] at h2
    exact commutatorElement_eq_one_iff_mul_comm.1 h2
  have hzmem := mem_pCore_of_forall_comm_aux Nat.prime_three
    (z := QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) (⟨j, hjJ⟩ : ↥J)) hcen
  exact (hψ ⟨j, hjJ⟩).2 hzmem

@[expose] def trivFrat (J R : Subgroup G) (hJR : J ≤ Subgroup.normalizer (R : Set G)) : Subgroup G where
  carrier := {j | j ∈ J ∧ ∀ r ∈ R, ⁅j, r⁆ ∈ frat2 R}
  one_mem' := ⟨J.one_mem, fun r _ => by
    rw [commutatorElement_one_left]
    exact (frat2 R).one_mem⟩
  mul_mem' := by
    rintro a b ⟨haJ, ha⟩ ⟨hbJ, hb⟩
    refine ⟨J.mul_mem haJ hbJ, fun r hr => ?_⟩
    have hid : ⁅a * b, r⁆ = a * ⁅b, r⁆ * a⁻¹ * ⁅a, r⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hid]
    refine (frat2 R).mul_mem ?_ (ha r hr)
    exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_frat2 hJR haJ) _).1 (hb r hr)
  inv_mem' := by
    rintro a ⟨haJ, ha⟩
    refine ⟨J.inv_mem haJ, fun r hr => ?_⟩
    have hid : ⁅a⁻¹, r⁆ = a⁻¹ * ⁅a, r⁆⁻¹ * a := by
      simp only [commutatorElement_def]
      group
    rw [hid]
    have h1 : a⁻¹ * ((⁅a, r⁆)⁻¹) * a⁻¹⁻¹ ∈ frat2 R :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_frat2 hJR (J.inv_mem haJ)) _).1
        ((frat2 R).inv_mem (ha r hr))
    simpa using h1

theorem trivFrat_normal (J R : Subgroup G) (hJR : J ≤ Subgroup.normalizer (R : Set G)) :
    ((trivFrat J R hJR).subgroupOf J).Normal := by
  have hle : trivFrat J R hJR ≤ J := fun k hk => hk.1
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle, Subgroup.le_normalizer_iff]
  intro g hg k hk
  refine ⟨J.mul_mem (J.mul_mem hg hk.1) (J.inv_mem hg), fun r hr => ?_⟩
  have hid : ⁅g * k * g⁻¹, r⁆ = g * ⁅k, g⁻¹ * r * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [hid]
  have hr' : g⁻¹ * r * g ∈ R := by
    simpa using (Subgroup.mem_normalizer_iff.1 (hJR (J.inv_mem hg)) r).1 hr
  have := hk.2 _ hr'
  have h2 := (Subgroup.mem_normalizer_iff.1 (le_normalizer_frat2 hJR hg) _).1 this
  simpa using h2

theorem mem_oPPrimeP_of_trivial_on_frat {L J Rs : Subgroup G} (hJL : J ≤ L)
    (hJlay : GLAPLayer 3 J = J) (hJR : J ≤ Subgroup.normalizer (Rs : Set G)) (hRs2 : IsPGroup 2 Rs)
    (hCL : L ⊓ Subgroup.centralizer (Rs : Set G) ≤ oPPrimeP 3 L) {j : G} (hj : j ∈ J)
    (h : ∀ r ∈ Rs, ⁅j, r⁆ ∈ frat2 Rs) : j ∈ oPPrimeP 3 J := by
  have hK₀J : trivFrat J Rs hJR ≤ J := fun k hk => hk.1
  have hpow : ∀ k ∈ trivFrat J Rs hJR, ∃ n : ℕ, k ^ (2 ^ n) ∈ oPPrimeP 3 J := by
    intro k hk
    obtain ⟨n, hn⟩ := burnside_frat hRs2 (hJR hk.1) hk.2
    refine ⟨n, ?_⟩
    have hJn : k ^ (2 ^ n) ∈ J := J.pow_mem hk.1 _
    exact inf_oPPrimeP_le Nat.prime_three hJL
      (Subgroup.mem_inf.2 ⟨hJn, hCL (Subgroup.mem_inf.2 ⟨hJL hJn, hn⟩)⟩)
  exact le_oPPrimeP_of_two_power hJlay hK₀J (trivFrat_normal J Rs hJR) hpow ⟨hj, h⟩

theorem mem_sup_of_two_element {J Rs : Subgroup G} (hJR : J ≤ Subgroup.normalizer (Rs : Set G))
    {j r : G} (hj : j ∈ oPPrimeP 3 J) (hr : r ∈ Rs) (h2 : ∃ n : ℕ, (j * r) ^ (2 ^ n) = 1) :
    j * r ∈ GLAPPrimeCoreOf 3 J ⊔ Rs := by
  obtain ⟨k, hk⟩ := oPPrimeP_pow_mem 3 J hj
  have hjJ : j ∈ J := Subgroup.map_subtype_le _ hj
  have hpow : ∀ m : ℕ, ∃ ρ ∈ Rs, (j * r) ^ m = ρ * j ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, Rs.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨ρ, hρ, hm⟩ := ih
      refine ⟨ρ * (j ^ (m + 1) * r * (j ^ (m + 1))⁻¹), Rs.mul_mem hρ ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 (hJR (J.pow_mem hjJ (m + 1))) r).1 hr
      · rw [pow_succ, hm, pow_succ j m]
        group
  obtain ⟨ρ, hρ, hx⟩ := hpow (3 ^ k)
  have hxmem : (j * r) ^ (3 ^ k) ∈ GLAPPrimeCoreOf 3 J ⊔ Rs := by
    rw [hx]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hρ) (Subgroup.mem_sup_left hk)
  obtain ⟨n, hn⟩ := h2
  have hord : orderOf (j * r) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have hcop : Nat.Coprime (3 ^ k) (orderOf (j * r)) := by
    have : Nat.Coprime (3 ^ k) (2 ^ n) := Nat.Coprime.pow k n (by norm_num)
    exact this.coprime_dvd_right hord
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact Subgroup.pow_mem _ hxmem m

theorem faithful_mod {A L J Rs T : Subgroup G} (hJL : J ≤ L) (hJlay : GLAPLayer 3 J = J)
    (hJR : J ≤ Subgroup.normalizer (Rs : Set G)) (hJA : J ≤ Subgroup.centralizer (A : Set G))
    (hJC : (⁅Rs ⊓ Subgroup.centralizer (A : Set G), J⁆ : Subgroup G) = ⊥)
    (hAR : A ≤ Subgroup.normalizer (Rs : Set G)) (hRs2 : IsPGroup 2 Rs) (hRT : Rs ≤ T)
    (hT2 : IsPGroup 2 T) (hTJ : T ≤ J ⊔ Rs) (hNn : ((hatN Rs A).subgroupOf T).Normal)
    (hCL : L ⊓ Subgroup.centralizer (Rs : Set G) ≤ oPPrimeP 3 L)
    (hT : T ⊓ (GLAPPrimeCoreOf 3 J ⊔ Rs) ≤ Rs) (hAel : IsElemAbelian 3 A) :
    ∀ t ∈ T, (∀ r ∈ Rs, ⁅t, r⁆ ∈ hatN Rs A) → t ∈ Rs := by
  intro t htT hcomm
  have hmul : (↑(J ⊔ Rs) : Set G) = (J : Set G) * (Rs : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right J Rs hJR
  have htJR : t ∈ (J : Set G) * (Rs : Set G) := by
    rw [← hmul]
    exact hTJ htT
  obtain ⟨j, hjJ, r₀, hr₀, hteq⟩ := Set.mem_mul.1 htJR
  have hjT : j ∈ T := by
    have h1 : j = t * r₀⁻¹ := by rw [← hteq]; group
    rw [h1]
    exact T.mul_mem htT (T.inv_mem (hRT hr₀))
  have hconjN : ∀ g ∈ T, ∀ n ∈ hatN Rs A, g * n * g⁻¹ ∈ hatN Rs A := by
    intro g hg n hn
    have h := hNn.conj_mem ⟨n, hRT (hatN_le Rs A hn)⟩ (Subgroup.mem_subgroupOf.2 hn) ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.1 h
  have hjr : ∀ r ∈ Rs, ⁅j, r⁆ ∈ hatN Rs A := by
    intro r hr
    have h1 := hcomm r hr
    rw [← hteq] at h1
    have hcN : ⁅r⁻¹, r₀⁆ ∈ hatN Rs A :=
      (commutator_le_frat2 Rs |>.trans (frat2_le_hatN Rs A))
        (Subgroup.commutator_mem_commutator (Rs.inv_mem hr) hr₀)
    have hid : ⁅j, r⁆ = ⁅j * r₀, r⁆ * (r * (j * ⁅r⁻¹, r₀⁆ * j⁻¹) * r⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [hid]
    exact (hatN Rs A).mul_mem h1 ((hatN Rs A).inv_mem
      (hconjN r (hRT hr) _ (hconjN j hjT _ hcN)))
  have hfrat := trivial_on_frat hRs2 hAel hAR hJR hJA hJC hjJ hjr
  have hjO := mem_oPPrimeP_of_trivial_on_frat hJL hJlay hJR hRs2 hCL hjJ hfrat
  have h2 : ∃ n : ℕ, (j * r₀) ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := hT2 ⟨t, htT⟩
    refine ⟨n, ?_⟩
    rw [hteq]
    have := congrArg Subtype.val hn
    simpa using this
  have hmem := mem_sup_of_two_element hJR hjO hr₀ h2
  rw [hteq] at hmem
  exact hT ⟨htT, hmem⟩

theorem fpf_mod {Rs A : Subgroup G} (hRs2 : IsPGroup 2 Rs) (hAel : IsElemAbelian 3 A)
    (hAR : A ≤ Subgroup.normalizer (Rs : Set G)) :
    ∀ r ∈ Rs, (∀ a ∈ A, ⁅r, a⁆ ∈ hatN Rs A) → r ∈ hatN Rs A := by
  intro r hr hfix
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAC : A ≤ Subgroup.centralizer (A : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact isElemAbelian_commute hAel ha hg
  have hRN : Rs ≤ Subgroup.normalizer (hatN Rs A : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    exact (Subgroup.commutator_mono le_rfl (hatN_le Rs A)).trans
      ((commutator_le_frat2 Rs).trans (frat2_le_hatN Rs A))
  have hAN : A ≤ Subgroup.normalizer (hatN Rs A : Set G) :=
    le_normalizer_sup (le_normalizer_frat2 hAR)
      (le_normalizer_inf hAR (hAC.trans Subgroup.le_normalizer))
  have hsolv : Group.IsSolvable ↥Rs := by
    haveI : Group.IsNilpotent ↥Rs := hRs2.isNilpotent
    infer_instance
  have hcop : (Nat.card A).Coprime (Nat.card Rs) := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := (isPGroup_of_isElemAbelian hAel).exists_card_eq
    obtain ⟨m, hm⟩ := hRs2.exists_card_eq
    rw [hk, hm]
    exact Nat.Coprime.pow k m (by norm_num)
  have hfix' : ∀ a ∈ A, r⁻¹ * (a * r * a⁻¹) ∈ hatN Rs A := by
    intro a ha
    have h1 := hfix a ha
    have e : r⁻¹ * (a * r * a⁻¹) = r⁻¹ * (⁅r, a⁆)⁻¹ * r⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (hRN (Rs.inv_mem hr)) _).1 ((hatN Rs A).inv_mem h1)
  obtain ⟨c, hc, n, hn, rfl⟩ :=
    CFSG.LocalAnalysis.EvenBN.Common.exists_mem_inf_centralizer_mul_of_coprime (hatN_le Rs A) hRN
      hAR hAN hsolv hcop hr hfix'
  exact (hatN Rs A).mul_mem (Subgroup.mem_sup_right hc) hn

theorem exists_D_nonabelian {B A T Rs N : Subgroup G} (h : HatSetup B A T Rs N) :
    ∃ D : Subgroup G, D ≤ B ∧ IsElemAbelian 3 D ∧ Nat.card D = 9 ∧
      ¬ (⁅T ⊓ Subgroup.centralizer (D : Set G), T ⊓ Subgroup.centralizer (D : Set G)⁆ :
        Subgroup G) ≤ N := by
  by_contra hcon
  push Not at hcon
  have hTN : T ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (h.NR.trans h.RT)).1 h.Nn
  have hT3 : Nat.Coprime 3 (Nat.card T) := by
    have h1 := hat_coprime_card h.Bc h.T2
    rw [h.Bc] at h1
    exact Nat.Coprime.coprime_dvd_left (dvd_pow_self 3 (by norm_num)) h1
  have hsup : ⨆ E ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes 3 B,
      T ⊓ Subgroup.centralizer (E : Set G) = T :=
    CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_hyperplanes Nat.prime_three h.Bel
      (by rw [h.Bc]; norm_num) h.BT hT3
  have hD : ∀ E₁ ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes 3 B,
      ∀ E₂ ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes 3 B,
      ∀ x ∈ T ⊓ Subgroup.centralizer (E₁ : Set G), ∀ y ∈ T ⊓ Subgroup.centralizer (E₂ : Set G),
        ⁅x, y⁆ ∈ N := by
    intro E₁ hE₁ E₂ hE₂ x hx y hy
    obtain ⟨hE₁B, hE₁c⟩ := hE₁
    obtain ⟨hE₂B, hE₂c⟩ := hE₂
    have h1 : Nat.card E₁ = 27 := by
      rw [h.Bc] at hE₁c
      omega
    have h2 : Nat.card E₂ = 27 := by
      rw [h.Bc] at hE₂c
      omega
    have hnorm : E₂ ≤ Subgroup.normalizer (E₁ : Set G) := by
      intro g hg
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact isElemAbelian_commute h.Bel (hE₁B he) (hE₂B hg)
    have hcard := card_sup_mul_card_inf_of_le_normalizer hnorm
    have hle81 : Nat.card (E₁ ⊔ E₂ : Subgroup G) ≤ 81 := by
      have h3 := Subgroup.card_le_of_le (sup_le hE₁B hE₂B)
      rw [h.Bc] at h3
      simpa using h3
    have hge9 : 9 ≤ Nat.card (E₁ ⊓ E₂ : Subgroup G) := by
      rw [h1, h2] at hcard
      by_contra hlt
      push Not at hlt
      nlinarith
    have hdvd27 : Nat.card (E₁ ⊓ E₂ : Subgroup G) ∣ 27 := h1 ▸ Subgroup.card_dvd_of_le inf_le_left
    have h9 : 3 ^ 2 ∣ Nat.card (E₁ ⊓ E₂ : Subgroup G) := by
      have hmem : Nat.card (E₁ ⊓ E₂ : Subgroup G) ∈ Nat.divisors 27 :=
        Nat.mem_divisors.2 ⟨hdvd27, by norm_num⟩
      have hd : Nat.divisors 27 = {1, 3, 9, 27} := by decide
      rw [hd] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h4 | h4 | h4 | h4 <;> rw [h4] <;> omega
    obtain ⟨D, hDcard, -, hDle⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three
      (n := 2) (H := ⊥) (L := E₁ ⊓ E₂) (by simp) h9 bot_le
    have hDB : D ≤ B := hDle.trans (inf_le_left.trans hE₁B)
    have hnab := hcon D hDB (isElemAbelian_mono h.Bel hDB) (by simpa using hDcard)
    have hxD : x ∈ T ⊓ Subgroup.centralizer (D : Set G) :=
      ⟨hx.1, Subgroup.centralizer_le (fun _ hd => (hDle hd).1) hx.2⟩
    have hyD : y ∈ T ⊓ Subgroup.centralizer (D : Set G) :=
      ⟨hy.1, Subgroup.centralizer_le (fun _ hd => (hDle hd).2) hy.2⟩
    exact hnab (Subgroup.commutator_mem_commutator hxD hyD)
  have hstep1 : ∀ E₂ ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes 3 B,
      ∀ y ∈ T ⊓ Subgroup.centralizer (E₂ : Set G), ∀ x ∈ T, ⁅x, y⁆ ∈ N := by
    intro E₂ hE₂ y hy x hx
    have hle : T ≤ hatModComm T N ((T ⊓ Subgroup.centralizer (E₂ : Set G) : Subgroup G) : Set G)
        hTN := by
      refine le_trans (le_of_eq hsup.symm) ?_
      exact iSup₂_le fun E₁ hE₁ x hx => ⟨hx.1, fun y hy => hD E₁ hE₁ E₂ hE₂ x hx y hy⟩
    exact (hle hx).2 y hy
  have hall : ∀ x ∈ T, ∀ y ∈ T, ⁅y, x⁆ ∈ N := by
    intro x hx y hy
    have hle : T ≤ hatModComm T N ({x} : Set G) hTN := by
      refine le_trans (le_of_eq hsup.symm) ?_
      refine iSup₂_le fun E₂ hE₂ y hy => ⟨hy.1, fun z hz => ?_⟩
      rw [Set.mem_singleton_iff.1 hz, ← commutatorElement_inv]
      exact N.inv_mem (hstep1 E₂ hE₂ y hy x hx)
    exact (hle hy).2 x rfl
  have hex : ∃ t ∈ T, t ∉ Rs := by
    by_contra hno
    push Not at hno
    have h1 := Subgroup.card_le_of_le (fun t ht => hno t ht : T ≤ Rs)
    have h2 : 0 < Nat.card Rs := Nat.card_pos
    have h3 := h.idx
    omega
  obtain ⟨t, htT, htR⟩ := hex
  exact htR (h.cR t htT fun r hr => by
    rw [← commutatorElement_inv]
    exact N.inv_mem (hall t htT r (h.RT hr)))

theorem hat_commutator_le {B A T Rs N : Subgroup G} (h : HatSetup B A T Rs N) :
    (⁅T, T⁆ : Subgroup G) ≤ Rs := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (Rs.subgroupOf T).Normal := h.Rn
  have hq : Nat.card (T ⧸ Rs.subgroupOf T) = 2 ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Rs.subgroupOf T)
    have h2 : Nat.card (Rs.subgroupOf T) = Nat.card Rs :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.RT).toEquiv
    have hpos : 0 < Nat.card Rs := Nat.card_pos
    rw [h2, h.idx] at h1
    have h3 := Nat.eq_of_mul_eq_mul_right hpos h1
    omega
  have hcomm : ∀ a b : T ⧸ Rs.subgroupOf T, a * b = b * a :=
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq hq).is_comm.comm
  rw [Subgroup.commutator_le]
  intro s hs t ht
  have hc : (QuotientGroup.mk (⁅(⟨s, hs⟩ : T), (⟨t, ht⟩ : T)⁆) : T ⧸ Rs.subgroupOf T) = 1 := by
    have e : (QuotientGroup.mk (⁅(⟨s, hs⟩ : T), (⟨t, ht⟩ : T)⁆) : T ⧸ Rs.subgroupOf T) =
        ⁅(QuotientGroup.mk (⟨s, hs⟩ : T) : T ⧸ Rs.subgroupOf T),
          (QuotientGroup.mk (⟨t, ht⟩ : T) : T ⧸ Rs.subgroupOf T)⁆ := rfl
    rw [e]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ _)
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hc)

theorem hat_centralizer_le {B A T Rs N : Subgroup G} (h : HatSetup B A T Rs N) :
    T ⊓ Subgroup.centralizer (B : Set G) ≤ Rs := by
  have hTR : T ≤ Subgroup.normalizer (Rs : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.RT).1 h.Rn
  rintro t ⟨htT, htC⟩
  by_contra htR
  have hBnc : ¬ ∀ b ∈ B, ∀ s ∈ T, ⁅b, s⁆ ∈ Rs := fun hall =>
    h.Bnc (Subgroup.commutator_le.2 hall)
  set M := hatModComm T Rs (B : Set G) hTR with hMdef
  have hRsM : Rs ≤ M := by
    intro r hr
    refine ⟨h.RT hr, fun b hb => ?_⟩
    have e : ⁅r, b⁆ = r * (b * r⁻¹ * b⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Rs.mul_mem hr ((Subgroup.mem_normalizer_iff.1 (h.BR hb) r⁻¹).1 (Rs.inv_mem hr))
  have htM : t ∈ M := by
    refine ⟨htT, fun b hb => ?_⟩
    have hc : b * t = t * b := Subgroup.mem_centralizer_iff.1 htC b hb
    rw [commutatorElement_eq_one_iff_mul_comm.2 hc.symm]
    exact Rs.one_mem
  have hcomm_sym : ∀ b ∈ B, ∀ s : G, ⁅s, b⁆ ∈ Rs → ⁅b, s⁆ ∈ Rs := by
    intro b _ s hs
    rw [← commutatorElement_inv]
    exact Rs.inv_mem hs
  have hcase : ¬ T ≤ M := by
    intro hTM
    exact hBnc fun b hb s hs => hcomm_sym b hb s ((hTM hs).2 b hb)
  set T₁ : Subgroup G := Rs ⊔ Subgroup.zpowers t with hT₁
  have hT₁T : T₁ ≤ T := sup_le h.RT (Subgroup.zpowers_le.2 htT)
  have hT₁M : T₁ ≤ M := sup_le hRsM (Subgroup.zpowers_le.2 htM)
  have hRspos : 0 < Nat.card Rs := Nat.card_pos
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le (le_sup_left : Rs ≤ T₁)
  have hcdvd : c ∣ 4 := by
    have h1 : Nat.card T₁ ∣ Nat.card T := Subgroup.card_dvd_of_le hT₁T
    rw [hc, h.idx, mul_comm 4] at h1
    exact Nat.dvd_of_mul_dvd_mul_left hRspos h1
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply htR
    have hEq : Rs = T₁ :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hc, mul_one])
    rw [hEq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hc4 : c ≠ 4 := by
    rintro rfl
    apply hcase
    have hEq : T₁ = T := Subgroup.eq_of_le_of_card_ge hT₁T (by rw [hc, h.idx, mul_comm])
    rw [← hEq]
    exact hT₁M
  have hc2 : c = 2 := by
    have : c ∈ Nat.divisors 4 := Nat.mem_divisors.2 ⟨hcdvd, by norm_num⟩
    have hd : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [hd] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  subst hc2
  have hrel : T₁.relIndex T = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := T₁) (K := T)
    rw [inf_eq_left.2 hT₁T, hc, h.idx] at h1
    have h2 : Nat.card Rs * (T₁.relIndex T * 2) = Nat.card Rs * 4 := by linarith
    have h3 := Nat.eq_of_mul_eq_mul_left hRspos h2
    omega
  have hidx2 : (T₁.subgroupOf T).index = 2 := hrel
  have hBz : B ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
    intro b hb
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro g ⟨k, rfl⟩
    have hbt : Commute b t := Subgroup.mem_centralizer_iff.1 htC b hb
    exact ((hbt.zpow_right k).eq).symm
  have hBT₁ : B ≤ Subgroup.normalizer (T₁ : Set G) := le_normalizer_sup h.BR hBz
  have hTB : ∀ s ∈ T, ∀ b ∈ B, ⁅s, b⁆ ∈ T₁ := by
    intro s hs b hb
    have hbs : b * s * b⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (h.BT hb) s).1 hs
    have key := Subgroup.mul_mem_iff_of_index_two hidx2 (a := (⟨b * s * b⁻¹, hbs⟩ : T))
      (b := ⟨s⁻¹, T.inv_mem hs⟩)
    have h1 : (⟨b * s * b⁻¹, hbs⟩ : T) ∈ T₁.subgroupOf T ↔
        (⟨s⁻¹, T.inv_mem hs⟩ : T) ∈ T₁.subgroupOf T := by
      simp only [Subgroup.mem_subgroupOf]
      rw [← Subgroup.mem_normalizer_iff.1 (hBT₁ hb) s]
      exact inv_mem_iff.symm
    have h2 := key.2 h1
    rw [Subgroup.mem_subgroupOf] at h2
    have e : ⁅s, b⁆ = (b * s * b⁻¹ * s⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact T₁.inv_mem h2
  have hdouble : (⁅⁅T, B⁆, B⁆ : Subgroup G) = ⁅T, B⁆ :=
    GL83.commutator_double_eq_self B T h.BT (hat_coprime_card h.Bc h.T2)
      (hat_isSolvable_of_isPGroup h.T2)
  have hTB' : (⁅T, B⁆ : Subgroup G) ≤ T₁ := Subgroup.commutator_le.2 hTB
  have hTB'' : (⁅T, B⁆ : Subgroup G) ≤ Rs := by
    calc (⁅T, B⁆ : Subgroup G) = ⁅⁅T, B⁆, B⁆ := hdouble.symm
      _ ≤ ⁅T₁, B⁆ := Subgroup.commutator_mono hTB' le_rfl
      _ ≤ Rs := Subgroup.commutator_le.2 fun s hs b hb => (hT₁M hs).2 b hb
  apply h.Bnc
  rw [Subgroup.commutator_comm]
  exact hTB''

theorem build_S {B A T Rs N D : Subgroup G} (h : HatSetup B A T Rs N)
    (hTT : (⁅T, T⁆ : Subgroup G) ≤ Rs) (hCB : T ⊓ Subgroup.centralizer (B : Set G) ≤ Rs)
    (hDB : D ≤ B) (hDel : IsElemAbelian 3 D) (hDc : Nat.card D = 9)
    (hnab : ¬ (⁅T ⊓ Subgroup.centralizer (D : Set G), T ⊓ Subgroup.centralizer (D : Set G)⁆ :
      Subgroup G) ≤ N) :
    ∃ S : Subgroup G, S ≤ T ⊓ Subgroup.centralizer (D : Set G) ∧ B ≤ Subgroup.normalizer (S : Set G) ∧
      (⁅B, S⁆ : Subgroup G) = S ∧ (⁅S, S⁆ : Subgroup G) ≤ Rs ∧
      (⁅B, (⁅S, S⁆ : Subgroup G)⁆ : Subgroup G) ≠ ⊥ ∧ Nat.card S ≤ 4 * Nat.card (S ⊓ Rs : Subgroup G) := by
  have hTN : T ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (h.NR.trans h.RT)).1 h.Nn
  have hTR : T ≤ Subgroup.normalizer (Rs : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.RT).1 h.Rn
  set C₀ : Subgroup G := T ⊓ Subgroup.centralizer (D : Set G) with hC₀
  have hBCD : B ≤ Subgroup.centralizer (D : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact isElemAbelian_commute h.Bel (hDB hd) hb
  have hBC₀ : B ≤ Subgroup.normalizer (C₀ : Set G) :=
    le_normalizer_inf h.BT (hBCD.trans Subgroup.le_normalizer)
  have hC₀T : C₀ ≤ T := inf_le_left
  have hC₀2 : IsPGroup 2 C₀ := h.T2.to_le hC₀T
  set S : Subgroup G := ⁅C₀, B⁆ with hS
  have hSC₀ : S ≤ C₀ := Subgroup.le_normalizer_iff_commutator_le_left.1 hBC₀
  have hBS : B ≤ Subgroup.normalizer (S : Set G) := Subgroup.normalizer_commutator_ge_right C₀ B
  have hBSS : (⁅B, S⁆ : Subgroup G) = S := by
    rw [Subgroup.commutator_comm B S]
    exact GL83.commutator_double_eq_self B C₀ hBC₀ (hat_coprime_card h.Bc hC₀2)
      (hat_isSolvable_of_isPGroup hC₀2)
  have hST : S ≤ T := hSC₀.trans hC₀T
  have hSSR : (⁅S, S⁆ : Subgroup G) ≤ Rs := (Subgroup.commutator_mono hST hST).trans hTT
  have hfix : ∀ r ∈ Rs, r ∈ Subgroup.centralizer (B : Set G) → r ∈ N := by
    intro r hr hrC
    refine h.fpf r hr fun a ha => ?_
    have hc : a * r = r * a := Subgroup.mem_centralizer_iff.1 hrC a (h.AB ha)
    rw [commutatorElement_eq_one_iff_mul_comm.2 hc.symm]
    exact N.one_mem
  have hCBN : C₀ ⊓ Subgroup.centralizer (B : Set G) ≤ N := fun x hx =>
    hfix x (hCB ⟨hx.1.1, hx.2⟩) hx.2
  have hfac : C₀ = ⁅C₀, B⁆ ⊔ (C₀ ⊓ Subgroup.centralizer (B : Set G)) :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
      Nat.prime_three B C₀ (isPGroup_of_isElemAbelian h.Bel) (hat_not_dvd_three hC₀2) hBC₀
  have hC₀SN : C₀ ≤ S ⊔ N :=
    calc C₀ = ⁅C₀, B⁆ ⊔ (C₀ ⊓ Subgroup.centralizer (B : Set G)) := hfac
      _ ≤ S ⊔ N := sup_le_sup le_rfl hCBN
  have hNmod : ∀ Y : Subgroup G, Y ≤ T → N ≤ hatModComm T N (Y : Set G) hTN := by
    intro Y hY n hn
    refine ⟨h.RT (h.NR hn), fun y hy => ?_⟩
    have e : ⁅n, y⁆ = n * (y * n⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem hn ((Subgroup.mem_normalizer_iff.1 (hTN (hY hy)) n⁻¹).1 (N.inv_mem hn))
  have hnotle : ¬ (⁅S, S⁆ : Subgroup G) ≤ N := by
    intro hSSN
    apply hnab
    have hM1 : S ⊔ N ≤ hatModComm T N (S : Set G) hTN :=
      sup_le (fun x hx => ⟨hST hx, fun y hy =>
        hSSN (Subgroup.commutator_mem_commutator hx hy)⟩) (hNmod S hST)
    have hM2 : S ⊔ N ≤ hatModComm T N (C₀ : Set G) hTN := by
      refine sup_le (fun y hy => ⟨hST hy, fun x hx => ?_⟩) (hNmod C₀ hC₀T)
      have h1 := (hM1 (hC₀SN hx)).2 y hy
      rw [← commutatorElement_inv]
      exact N.inv_mem h1
    exact Subgroup.commutator_le.2 fun x hx y hy => (hM2 (hC₀SN hx)).2 y hy
  refine ⟨S, hSC₀, hBS, hBSS, hSSR, ?_, ?_⟩
  · intro hbot
    apply hnotle
    have hcen : (⁅S, S⁆ : Subgroup G) ≤ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.commutator_comm] at hbot
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
    intro x hx
    exact hfix x (hSSR hx) (hcen hx)
  · have hSR : S ≤ Subgroup.normalizer (Rs : Set G) := hST.trans hTR
    have hcard := card_sup_mul_card_inf_of_le_normalizer hSR
    have hle : Nat.card (Rs ⊔ S : Subgroup G) ≤ 4 * Nat.card Rs := by
      rw [← h.idx]
      exact Subgroup.card_le_of_le (sup_le h.RT hST)
    have hRspos : 0 < Nat.card Rs := Nat.card_pos
    rw [inf_comm]
    have h1 : Nat.card Rs * Nat.card S ≤ Nat.card Rs * (4 * Nat.card (Rs ⊓ S : Subgroup G)) :=
      calc Nat.card Rs * Nat.card S
          = Nat.card (Rs ⊔ S : Subgroup G) * Nat.card (Rs ⊓ S : Subgroup G) := hcard.symm
        _ ≤ (4 * Nat.card Rs) * Nat.card (Rs ⊓ S : Subgroup G) := Nat.mul_le_mul_right _ hle
        _ = Nat.card Rs * (4 * Nat.card (Rs ⊓ S : Subgroup G)) := by ring
    exact Nat.le_of_mul_le_mul_left h1 hRspos

theorem abstract_hat {B A T Rs N : Subgroup G} (h : HatSetup B A T Rs N) :
    ∃ D S : Subgroup G, D ≤ B ∧ IsElemAbelian 3 D ∧ Nat.card D = 9 ∧
      S ≤ T ⊓ Subgroup.centralizer (D : Set G) ∧ B ≤ Subgroup.normalizer (S : Set G) ∧
      (⁅B, S⁆ : Subgroup G) = S ∧ (⁅S, S⁆ : Subgroup G) ≤ Rs ∧
      (⁅B, (⁅S, S⁆ : Subgroup G)⁆ : Subgroup G) ≠ ⊥ ∧
      Nat.card S ≤ 4 * Nat.card (S ⊓ Rs : Subgroup G) := by
  obtain ⟨D, hDB, hDel, hDc, hnab⟩ := exists_D_nonabelian h
  obtain ⟨S, hST, hBS, hBSS, hSSR, hne, hidx⟩ :=
    build_S h (hat_commutator_le h) (hat_centralizer_le h) hDB hDel hDc hnab
  exact ⟨D, S, hDB, hDel, hDc, hST, hBS, hBSS, hSSR, hne, hidx⟩

end CFSG.LocalAnalysis.GLTheoremA
