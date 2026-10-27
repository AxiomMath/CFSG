module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem522Y
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem515
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518DLO

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem inf_normalizer_le_normalizer_inf_K_F4 (h510 : Stmt5_1_10_F4) :
    M ⊓ Subgroup.normalizer (oTwoUpper H : Set G) ≤
      Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := h.hyp.toHyp5_0_1
  obtain ⟨-, -, hBorel, -⟩ := h510 G T M L H B D n h.hyp h.notation59
  have hMK := h.hyp.borel_eq hBorel
  have hTK := h.isSylowTwoOf_inf_K
  have hTKM : T ⊓ oTwoUpper H ≤ M ⊓ oTwoUpper H := inf_le_inf_right _ hh.T_le
  have hMKN :
      M ⊓ oTwoUpper H ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
    rw [hMK]
    exact inf_le_right
  have hTsyl : IsSylowTwoOf (T ⊓ oTwoUpper H) (M ⊓ oTwoUpper H) :=
    A4.isSylowTwoOf_mono hTK hTKM inf_le_right
  have hO : pCoreOf 2 (M ⊓ oTwoUpper H) = T ⊓ oTwoUpper H :=
    le_antisymm (F7.isSylowTwoOf_pCoreOf_le hTsyl)
      (le_pCoreOf_of_le_normalizer 2 hTKM hMKN hTK.2.1)
  have h1 : M ⊓ Subgroup.normalizer (oTwoUpper H : Set G) ≤
      Subgroup.normalizer ((M ⊓ oTwoUpper H : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans Subgroup.le_normalizer) inf_le_right).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  rw [← hO]
  exact h1.trans (normalizer_le_normalizer_pCoreOf 2 _)

theorem DBT_le_normalizer_inf_K_of_le_F4 (h510 : Stmt5_1_10_F4) {D' : Subgroup G} (hD'D : D' ≤ D)
    (hD' : D' ≤ Subgroup.normalizer (oTwoUpper H : Set G)) :
    D' ⊔ B ⊔ T ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) :=
  (le_inf (h.DBT_le_M_of_le hD'D) (h.DBT_le_Mp_of_le hD')).trans
    (h.inf_normalizer_le_normalizer_inf_K_F4 h510)

theorem DBT_le_normalizer_inf_K_F4 (h510 : Stmt5_1_10_F4)
    (hD : D ≤ Subgroup.normalizer (oTwoUpper H : Set G)) :
    D ⊔ B ⊔ T ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) :=
  h.DBT_le_normalizer_inf_K_of_le_F4 h510 le_rfl hD

theorem DBT_le_normalizer_inf_L_of_le_F4 (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    {D' : Subgroup G} (hD'D : D' ≤ D) :
    D' ⊔ B ⊔ T ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  have hh := h.hyp.toHyp5_0_1
  refine sup_le (sup_le ?_ ?_) hh.T_le_normalizer_inf
  · exact hD'D.trans (h.notation59.2.1.1.trans inf_le_right)
  · exact (h.notation59.1.1.trans (le_of_eq (inf_comm M H))).trans
      (hh.inf_le_normalizer_inf_F4 h331 hR h.hyp.hStar)

theorem S_facts_of_le_F4 (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    {D' : Subgroup G} (hD'D : D' ≤ D) (hD' : D' ≤ Subgroup.normalizer (oTwoUpper H : Set G)) :
    pCoreOf 2 (D' ⊔ B ⊔ T) ≤ T ∧ T ⊓ L ≤ pCoreOf 2 (D' ⊔ B ⊔ T) ∧
      T ⊓ oTwoUpper H ≤ pCoreOf 2 (D' ⊔ B ⊔ T) ∧ pCoreOf 2 M ≤ pCoreOf 2 (D' ⊔ B ⊔ T) ∧
      pCoreOf 2 (Subgroup.normalizer (oTwoUpper H : Set G)) ≤ pCoreOf 2 (D' ⊔ B ⊔ T) ∧
      D' ⊔ B ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (D' ⊔ B ⊔ T) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := h.hyp.toHyp5_0_1
  have hTX : T ≤ D' ⊔ B ⊔ T := le_sup_right
  have hT2 : IsPGroup 2 T := hh.sylow.1
  refine ⟨F7.isSylowTwoOf_pCoreOf_le (hh.isSylowTwoOf hTX), ?_, ?_, ?_, ?_,
    le_normalizer_pCoreOf 2 _⟩
  · exact le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans hTX)
      (h.DBT_le_normalizer_inf_L_of_le_F4 h331 hR hD'D) (hT2.to_le inf_le_left)
  · exact le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans hTX)
      (h.DBT_le_normalizer_inf_K_of_le_F4 h510 hD'D hD') (hT2.to_le inf_le_left)
  · exact le_pCoreOf_of_le_normalizer 2
      ((F7.isSylowTwoOf_pCoreOf_le (hh.isSylowTwoOf hh.T_le)).trans hTX)
      ((h.DBT_le_M_of_le hD'D).trans (le_normalizer_pCoreOf 2 M)) (pCoreOf_isPGroup 2 M)
  · exact le_pCoreOf_of_le_normalizer 2
      ((F7.isSylowTwoOf_pCoreOf_le (hh.isSylowTwoOf h.T_le_Mp)).trans hTX)
      ((h.DBT_le_Mp_of_le hD').trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)

theorem S_facts_F4 (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    (hD : D ≤ Subgroup.normalizer (oTwoUpper H : Set G)) :
    pCoreOf 2 (D ⊔ B ⊔ T) ≤ T ∧ T ⊓ L ≤ pCoreOf 2 (D ⊔ B ⊔ T) ∧
      T ⊓ oTwoUpper H ≤ pCoreOf 2 (D ⊔ B ⊔ T) ∧ pCoreOf 2 M ≤ pCoreOf 2 (D ⊔ B ⊔ T) ∧
      pCoreOf 2 (Subgroup.normalizer (oTwoUpper H : Set G)) ≤ pCoreOf 2 (D ⊔ B ⊔ T) ∧
      D ⊔ B ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (D ⊔ B ⊔ T) : Set G) :=
  h.S_facts_of_le_F4 h510 h331 hR le_rfl hD

theorem quotConjAut_eq_conj_of_mem_S_of_le_F4 (hTA : L34TwoAutFact) (h510 : Stmt5_1_10_F4)
    (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) {D' : Subgroup G} (hD'D : D' ≤ D)
    (hD : D' ≤ Subgroup.normalizer (oTwoUpper H : Set G)) {d₀ : G} (hd₀D : d₀ ∈ D')
    (hd₀3 : d₀ ^ 3 = 1) (hd₀ : ∀ k ∈ oTwoUpper H, d₀ * k⁻¹ ∉ centralizerModO2 (oTwoUpper H))
    {s : G} (hs : s ∈ pCoreOf 2 (D' ⊔ B ⊔ T))
    (hsN : s ∈ Subgroup.normalizer (oTwoUpper H : Set G)) :
    ∃ x ∈ imgO2 (oTwoUpper H) (T ⊓ oTwoUpper H),
      quotConjAut (oTwoUpper H) ⟨s, hsN⟩ = MulAut.conj x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper H with hKdef
  set S := pCoreOf 2 (D' ⊔ B ⊔ T) with hSdef
  obtain ⟨hST, -, hTKS, -, -, hSN⟩ := h.S_facts_of_le_F4 h510 h331 hR hD'D hD
  have hS2 : IsPGroup 2 S := pCoreOf_isPGroup 2 _
  have hTK := h.isSylowTwoOf_inf_K
  have hOTK : pCoreOf 2 K ≤ T ⊓ K := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTK
  have hd₀N : d₀ ∈ Subgroup.normalizer (K : Set G) := hD hd₀D
  have hBX : B ≤ D' ⊔ B ⊔ T := le_sup_right.trans le_sup_left
  have hDX : D' ≤ D' ⊔ B ⊔ T := le_sup_left.trans le_sup_left
  have hB3 : Nat.card B = 3 := h.card_B_eq_three_F4 h510
  obtain ⟨b₀, hb₀B, hb₀1⟩ : ∃ b₀ ∈ B, b₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : B = ⊥ := (Subgroup.eq_bot_iff_forall B).mpr hcon
    rw [hbot, Subgroup.card_bot] at hB3
    omega
  have hb₀K : b₀ ∈ K := h.mem_K_of_mem_B hb₀B
  have hb₀N : b₀ ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
    h.DBT_le_normalizer_inf_K_of_le_F4 h510 hD'D hD (hBX hb₀B)
  have hsT : s ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hST hs), hsN⟩
  obtain ⟨x, hx, hxe⟩ := hTA (O2Q K) h.l34 _ (isSylowTwoOf_imgO2 hTK)
    (quotConjAut K ⟨s, hsN⟩) (quotConjAut K ⟨d₀, hd₀N⟩)
    (exists_quotConjAut_pow_eq_one hS2 hs hsN)
    (map_quotConjAut_imgO2 inf_le_right ⟨s, hsN⟩ hsT)
    (by
      have e : (⟨d₀, hd₀N⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
        Subtype.ext (by simpa using hd₀3)
      rw [← map_pow, e, map_one])
    (by
      rintro ⟨q, hq⟩
      induction q using QuotientGroup.induction_on with
      | H k =>
        apply hd₀ k k.2
        have h1 : quotConjAut K (⟨d₀, hd₀N⟩ * ⟨k, Subgroup.le_normalizer k.2⟩⁻¹) = 1 := by
          rw [map_mul, map_inv, quotConjAut_of_mem k, ← hq, mul_inv_cancel]
        exact mem_centralizerModO2_of_quotConjAut_eq_one h1)
    (by
      have hc : s * d₀ * s⁻¹ * d₀⁻¹ ∈ S := by
        have h1 : d₀ * s⁻¹ * d₀⁻¹ ∈ S :=
          (Subgroup.mem_normalizer_iff.mp (hSN (hDX hd₀D)) _).mp (S.inv_mem hs)
        have := S.mul_mem hs h1
        simpa [mul_assoc] using this
      obtain ⟨m, hm⟩ := exists_quotConjAut_pow_eq_one (K := K) hS2 hc
        ((Subgroup.normalizer (K : Set G)).mul_mem ((Subgroup.normalizer (K : Set G)).mul_mem
          ((Subgroup.normalizer (K : Set G)).mul_mem hsN hd₀N)
          ((Subgroup.normalizer (K : Set G)).inv_mem hsN))
          ((Subgroup.normalizer (K : Set G)).inv_mem hd₀N))
      refine ⟨m, ?_⟩
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact hm)
    _ (mk_mem_normalizer_imgO2 inf_le_right hb₀K hb₀N)
    (by
      rw [mk_mem_imgO2_iff hOTK]
      intro hb
      apply hb₀1
      have h2 : ∃ m : ℕ, b₀ ^ 2 ^ m = 1 := by
        obtain ⟨m, hm⟩ := (h.hyp.toHyp5_0_1.sylow.1.to_le inf_le_left) ⟨b₀, hb⟩
        exact ⟨m, by simpa using congrArg Subtype.val hm⟩
      obtain ⟨m, hm⟩ := h2
      have hodd : Odd (orderOf b₀) := by
        have h1 : orderOf b₀ ∣ Nat.card B := by
          rw [← Subgroup.orderOf_mk b₀ hb₀B]
          exact orderOf_dvd_natCard _
        exact h.notation59.1.2.1.of_dvd_nat h1
      have hd : orderOf b₀ ∣ Nat.gcd (2 ^ m) (orderOf b₀) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm) dvd_rfl
      rw [Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)] at hd
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd))
    (by
      have hsb : s * b₀ * s⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hsN b₀).mp hb₀K
      have hc : s * b₀ * s⁻¹ * b₀⁻¹ ∈ T ⊓ K := by
        refine ⟨hST ?_, K.mul_mem hsb (K.inv_mem hb₀K)⟩
        have h1 : b₀ * s⁻¹ * b₀⁻¹ ∈ S :=
          (Subgroup.mem_normalizer_iff.mp (hSN (hBX hb₀B)) _).mp (S.inv_mem hs)
        have := S.mul_mem hs h1
        simpa [mul_assoc] using this
      have e : quotConjAut K ⟨s, hsN⟩ (QuotientGroup.mk ⟨b₀, hb₀K⟩) *
          (QuotientGroup.mk ⟨b₀, hb₀K⟩ : O2Q K)⁻¹ =
          QuotientGroup.mk (⟨s * b₀ * s⁻¹ * b₀⁻¹, hc.2⟩ : ↥K) := by
        rw [quotConjAut_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        rfl
      rw [e]
      exact mk_mem_imgO2 hc.2 hc)
  exact ⟨x, hx, hxe⟩

theorem quotConjAut_eq_conj_of_mem_S_F4 (hTA : L34TwoAutFact) (h510 : Stmt5_1_10_F4)
    (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    (hD : D ≤ Subgroup.normalizer (oTwoUpper H : Set G)) {d₀ : G} (hd₀D : d₀ ∈ D)
    (hd₀3 : d₀ ^ 3 = 1) (hd₀ : ∀ k ∈ oTwoUpper H, d₀ * k⁻¹ ∉ centralizerModO2 (oTwoUpper H))
    {s : G} (hs : s ∈ pCoreOf 2 (D ⊔ B ⊔ T))
    (hsN : s ∈ Subgroup.normalizer (oTwoUpper H : Set G)) :
    ∃ x ∈ imgO2 (oTwoUpper H) (T ⊓ oTwoUpper H),
      quotConjAut (oTwoUpper H) ⟨s, hsN⟩ = MulAut.conj x :=
  h.quotConjAut_eq_conj_of_mem_S_of_le_F4 hTA h510 h331 hR le_rfl hD hd₀D hd₀3 hd₀ hs hsN

theorem exists_parabolic_F4 (hPF : L34ParabolicFact) (hTA : L34TwoAutFact) (h510 : Stmt5_1_10_F4)
    (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact)
    (hD : D ≤ Subgroup.normalizer (oTwoUpper H : Set G)) {d₀ : G} (hd₀D : d₀ ∈ D)
    (hd₀3 : d₀ ^ 3 = 1) (hd₀ : ∀ k ∈ oTwoUpper H, d₀ * k⁻¹ ∉ centralizerModO2 (oTwoUpper H)) :
    ∃ U : Subgroup G, pCoreOf 2 (oTwoUpper H) ≤ U ∧ U ≤ T ⊓ oTwoUpper H ∧
      (∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 (oTwoUpper H)) ∧
      (∀ x ∈ U, x ^ 2 ∈ pCoreOf 2 (oTwoUpper H)) ∧
      Nat.card U = 16 * Nat.card (pCoreOf 2 (oTwoUpper H)) ∧
      D ⊔ B ⊔ pCoreOf 2 (D ⊔ B ⊔ T) ≤ Subgroup.normalizer (U : Set G) ∧
      ∃ φ : ↥(oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) →*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2),
        Function.Surjective φ ∧
          φ.ker = U.subgroupOf (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper H with hKdef
  set S := pCoreOf 2 (D ⊔ B ⊔ T) with hSdef
  obtain ⟨hST, -, -, -, -, -⟩ := h.S_facts_F4 h510 h331 hR hD
  have hTK := h.isSylowTwoOf_inf_K
  have hOTK : pCoreOf 2 K ≤ T ⊓ K := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTK
  have hBX : B ≤ D ⊔ B ⊔ T := le_sup_right.trans le_sup_left
  have hDX : D ≤ D ⊔ B ⊔ T := le_sup_left.trans le_sup_left
  have hXN := h.DBT_le_normalizer_inf_K_F4 h510 hD
  obtain ⟨P, R, hNP, hRS, hNR, hRab, hR16, ⟨π, hπs, hπk⟩, hodd⟩ :=
    hPF (O2Q K) h.l34 _ (isSylowTwoOf_imgO2 hTK)
  set U := preimageModTwoCore K R with hUdef
  have hUK : U ≤ K := preimageModTwoCore_le K R
  have hOU : pCoreOf 2 K ≤ U := pCoreOf_le_preimageModTwoCore K R
  have hUTK : U ≤ T ⊓ K :=
    (preimageModTwoCore_mono hRS).trans (preimageModTwoCore_imgO2 hOTK inf_le_right).le
  have hRU : imgO2 K U = R := imgO2_preimageModTwoCore K R
  have hoddN : ∀ g ∈ Subgroup.normalizer (K : Set G),
      g ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) → Odd (orderOf g) →
        g ∈ Subgroup.normalizer (U : Set G) := by
    intro g hgK hgT hgo
    apply mem_normalizer_preimageModTwoCore ⟨g, hgK⟩
    apply hodd
    · refine hgo.of_dvd_nat ((orderOf_map_dvd _ _).trans ?_)
      rw [Subgroup.orderOf_mk]
    · exact map_quotConjAut_imgO2 inf_le_right ⟨g, hgK⟩ hgT
  have hoddD : ∀ x ∈ D, Odd (orderOf x) := fun x hx =>
    h.notation59.2.1.2.1.of_dvd_nat
      (by rw [← Subgroup.orderOf_mk x hx]; exact orderOf_dvd_natCard _)
  have hoddB : ∀ x ∈ B, Odd (orderOf x) := fun x hx =>
    h.notation59.1.2.1.of_dvd_nat (by rw [← Subgroup.orderOf_mk x hx]; exact orderOf_dvd_natCard _)
  have hBK : B ≤ Subgroup.normalizer (K : Set G) :=
    h.notation59.1.1.trans (inf_le_right.trans (le_normalizer_oTwoUpper H))
  have hTMp := h.T_le_Mp
  refine ⟨U, hOU, hUTK, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx y hy
    obtain ⟨hxK, hxR⟩ := mem_preimageModTwoCore.mp hx
    obtain ⟨hyK, hyR⟩ := mem_preimageModTwoCore.mp hy
    have hmem : x * y * x⁻¹ * y⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem hxK hyK) (K.inv_mem hxK)) (K.inv_mem hyK)
    rw [mem_pCoreOf_iff_mk_eq_one hmem]
    have e : (⟨x * y * x⁻¹ * y⁻¹, hmem⟩ : ↥K) =
        ⟨x, hxK⟩ * ⟨y, hyK⟩ * (⟨x, hxK⟩ : ↥K)⁻¹ * (⟨y, hyK⟩ : ↥K)⁻¹ := rfl
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv]
    have hc : (QuotientGroup.mk ⟨x, hxK⟩ : O2Q K) * QuotientGroup.mk ⟨y, hyK⟩ =
        QuotientGroup.mk ⟨y, hyK⟩ * QuotientGroup.mk ⟨x, hxK⟩ :=
      congrArg Subtype.val (hRab.1.is_comm.comm ⟨_, hxR⟩ ⟨_, hyR⟩)
    rw [hc]
    group
  ·
    intro x hx
    obtain ⟨hxK, hxR⟩ := mem_preimageModTwoCore.mp hx
    rw [mem_pCoreOf_iff_mk_eq_one (K.pow_mem hxK 2)]
    have e : (⟨x ^ 2, K.pow_mem hxK 2⟩ : ↥K) = (⟨x, hxK⟩ : ↥K) ^ 2 := rfl
    rw [e, QuotientGroup.mk_pow]
    exact hRab.2 _ hxR
  · rw [card_preimageModTwoCore, hR16]
  · refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      exact hoddN x (hD hx) (hXN (hDX hx)) (hoddD x hx)
    · intro x hx
      exact hoddN x (hBK hx) (hXN (hBX hx)) (hoddB x hx)
    · intro s hs
      have hsN : s ∈ Subgroup.normalizer (K : Set G) := hTMp (hST hs)
      obtain ⟨x, hx, hxe⟩ := h.quotConjAut_eq_conj_of_mem_S_F4 hTA h510 h331 hR hD hd₀D hd₀3 hd₀ hs hsN
      apply mem_normalizer_preimageModTwoCore ⟨s, hsN⟩
      rw [hxe]
      have hxR : x ∈ Subgroup.normalizer (R : Set (O2Q K)) := hNR ▸ hNP (Subgroup.le_normalizer hx)
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hxR
  ·
    have hP : ∀ x : ↥(K ⊓ Subgroup.normalizer (U : Set G)),
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Subgroup.inclusion inf_le_left) x) ∈ P := by
      intro x
      rw [← hNR, ← hRU]
      exact mk_mem_normalizer_imgO2 hUK x.2.1 x.2.2
    let ψ : ↥(K ⊓ Subgroup.normalizer (U : Set G)) →* ↥P :=
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Subgroup.inclusion inf_le_left)).codRestrict P hP
    refine ⟨π.comp ψ, ?_, ?_⟩
    · intro q
      obtain ⟨⟨y, hyP⟩, rfl⟩ := hπs q
      induction y using QuotientGroup.induction_on with
      | H k =>
        have hkN : (k : G) ∈ Subgroup.normalizer (U : Set G) := by
          refine mem_normalizer_preimageModTwoCore (K := K)
            (⟨(k : G), Subgroup.le_normalizer k.2⟩ : ↥(Subgroup.normalizer (K : Set G))) ?_
          rw [quotConjAut_of_mem k]
          have hkR : (QuotientGroup.mk k : O2Q K) ∈ Subgroup.normalizer (R : Set (O2Q K)) :=
            hNR ▸ hyP
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hkR
        exact ⟨⟨k, k.2, hkN⟩, congrArg π (Subtype.ext rfl)⟩
    · ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hπk,
        Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        exact mem_preimageModTwoCore.mpr ⟨x.2.1, hx⟩
      · intro hx
        exact (mem_preimageModTwoCore.mp hx).2

end Hyp5_1_14

end Setting

end CFSG.Quasithin.H13
