module

public import CFSG.Quasithin.H13.U3S1348R
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1342
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1348I

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem s134_two_three_F4 (h139 : A6.Stmt13_3_9_F4) (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {z : G}
    (hz : z ∈ fsuV1 T V) (hzL : z ∉ centralizer (L : Set G)) {H : Subgroup G}
    (hHz : InHz T L V z H) (h3 : (H ⊓ normalizer (L : Set G)).relIndex H = 3) :
    ∀ x ∈ H, Nat.Coprime (orderOf x) 6 → x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTsyl, -, hHzC, hO2H, hHM⟩ := s134_inHz_facts S hHz
  set Y := closure {x : G | x ∈ H ∧ Nat.Coprime (orderOf x) 6} with hY
  have hYH : Y ≤ H := (closure_le _).2 fun x hx => hx.1
  have hYM : Y ≤ normalizer (L : Set G) := by
    refine (closure_le _).2 fun x ⟨hxH, hco⟩ => ?_
    obtain ⟨a, ha0, ha3, hxa⟩ := exists_pow_mem_of_relIndex_three h3 hxH
    have hco' : Nat.Coprime a (orderOf x) := by
      have hdvd : a ∣ 6 := by interval_cases a <;> norm_num
      exact (Nat.Coprime.coprime_dvd_right hdvd hco).symm
    exact (mem_of_pow_mem_of_coprime hxa hco').2
  have hY2 : oTwoRes Y = Y := by
    refine le_antisymm (oTwoRes_le _) ((closure_le _).2 fun x hx => ?_)
    have hodd : Odd (orderOf x) := by
      have := Nat.Coprime.coprime_dvd_right (show 2 ∣ 6 by norm_num) hx.2
      exact Nat.coprime_two_right.1 this
    exact mem_oTwoRes_of_odd (subset_closure hx) hodd (pow_orderOf_eq_one x)
  have hHY : H ≤ normalizer (Y : Set G) := by
    refine A5.le_normalizer_of_forall_conj_mem fun h hh y hy => ?_
    induction hy using closure_induction with
    | mem x hx =>
      refine subset_closure ⟨mul_mem (mul_mem hh hx.1) (inv_mem hh), ?_⟩
      have e : orderOf (h * x * h⁻¹) = orderOf x := by
        rw [show h * x * h⁻¹ = (MulAut.conj h).toMonoidHom x from rfl,
          orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective]
      rw [e]
      exact hx.2
    | one => simp
    | mul a b _ _ ha hb =>
      have e : h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by group
      rw [e]
      exact mul_mem ha hb
    | inv a _ ha =>
      have e : h * a⁻¹ * h⁻¹ = (h * a * h⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem ha
  rcases h139 G T L V H Y z S.h13 S.irr (s134_isA6On S) ⟨hTsyl.1, hO2H⟩ hHM hY2 hYH hHY hz hzL
    (le_inf hYM (hYH.trans hHzC)) with hY1 | ⟨-, hYL1, -⟩
  · intro x hx hco
    have : x ∈ Y := subset_closure ⟨hx, hco⟩
    rw [hY1] at this
    exact (mem_bot).1 this
  ·
    intro x hx hco
    have hxY : x ∈ Y := subset_closure ⟨hx, hco⟩
    rw [hYL1 he] at hxY
    have hxN : x ∈ normalizer (V : Set G) :=
      S.frame.L_le (((oTwoRes_le _).trans inf_le_left) hxY)
    have hA4 := s134_rho_L1 S hxN hxY
    have hρ6 := inA4_pow_six _ hA4
    have hρm : S.frame.ρ ⟨x, hxN⟩ ^ orderOf x = 1 := by
      rw [← map_pow]
      have : (⟨x, hxN⟩ : ↥(normalizer (V : Set G))) ^ orderOf x = 1 :=
        Subtype.ext (by simp)
      rw [this, map_one]
    have hρ1 := pow_gcd_eq_one.2 ⟨hρm, hρ6⟩
    rw [Nat.Coprime.gcd_eq_one hco, pow_one] at hρ1
    have hxC : x ∈ centralizer (V : Set G) := (s134_rho_eq_one_iff S _).1 hρ1
    have hxO : x ∈ pCoreOf 2 L := by
      rw [s134_pCoreOf_L_eq S he]
      exact ⟨((oTwoRes_le _).trans inf_le_left) hxY, hxC⟩
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨x, hxO⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hg := pow_gcd_eq_one.2 ⟨pow_orderOf_eq_one x, hk'⟩
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k
      (Nat.Coprime.coprime_dvd_right (show 2 ∣ 6 by norm_num) hco)), pow_one] at hg
    exact hg

theorem s134_HM_eq_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1228 : Stmt12_2_8_F4)
    (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {z : G}
    (hz : z ∈ fsuV1 T V) (hzL : z ∉ centralizer (L : Set G)) {H : Subgroup G}
    (hHz : InHz T L V z H) (h23 : ∀ x ∈ H, Nat.Coprime (orderOf x) 6 → x = 1) :
    H ⊓ normalizer (L : Set G) = L₁Of L (fsuV1 T V) ⊔ T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set X := H ⊓ normalizer (L : Set G) with hX
  obtain ⟨hTsyl, hL1TH, hHzC, -, -⟩ := s134_inHz_facts S hHz
  have hL1X : L₁ ≤ X :=
    le_inf (le_sup_left.trans hL1TH) ((oTwoRes_le _).trans (inf_le_left.trans le_normalizer))
  have hTX : T ≤ X := le_inf hTsyl.1 S.T_le_NL
  refine le_antisymm ?_ (sup_le hL1X hTX)

  have hXN : X ≤ normalizer (L₁ : Set G) := by
    refine A5.le_normalizer_oTwoRes_of_le_normalizer fun x hx => ?_
    have hxz : x * z = z * x := mem_centralizer_singleton_iff.1 (hHzC hx.1)
    have hxzV : x * S.zV = S.zV * x := by
      have h1 : x * S.zV * x⁻¹ = S.zV :=
        S.conj_zV ⟨x, A6.Setting134.normalizer_L_le_F4 S h1222 hx.2⟩
      calc x * S.zV = (x * S.zV * x⁻¹) * x := by group
        _ = S.zV * x := by rw [h1]
    have hxV1 := s134_mem_centralizer_V1 S hz hzL hxz hxzV
    exact mem_normalizer_inf_of hx.2 (le_normalizer (centralizer_le_normalizer _ hxV1))
  have hLn : (L₁.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hL1X).2 hXN

  have h3el : ∀ y ∈ H, (∃ m, Odd m ∧ y ^ m = 1) → ∃ k : ℕ, y ^ 3 ^ k = 1 := by
    rintro y hy ⟨m, hm, hym⟩
    obtain ⟨b, m', hm', hmm⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' 3 (by norm_num)
    refine ⟨b, h23 _ (pow_mem hy _) ?_⟩
    have hdvd : orderOf (y ^ 3 ^ b) ∣ m' := orderOf_dvd_of_pow_eq_one (by
      rw [← pow_mul, ← hmm, pow_orderOf_eq_one])
    have hodd : Odd (orderOf y) := hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hym)
    have hm'odd : Odd m' := hodd.of_dvd_nat (Dvd.intro_left _ hmm.symm)
    have hco : Nat.Coprime m' 6 := by
      rw [show (6 : ℕ) = 2 * 3 from rfl]
      exact Nat.Coprime.mul_right (Nat.coprime_two_right.2 hm'odd)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm').symm
    exact Nat.Coprime.coprime_dvd_left hdvd hco

  have hQ2 : IsPGroup 2 (↥X ⧸ L₁.subgroupOf X) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, hy, z', hz', hxyz, ⟨k, hyk⟩, m, hm, hzm⟩ := exists_two_odd_decomp (x : G)
    have hzX : z' ∈ X := zpowers_le.2 x.2 hz'
    have hyX : y ∈ X := zpowers_le.2 x.2 hy
    have hz'L1 : z' ∈ L₁ := s134_mem_L1_of_three_F4 h1332 h1228 S he hz hzL hzX.2 (hHzC hzX.1)
      (h3el z' hzX.1 ⟨m, hm, hzm⟩)
    have e : ((x : ↥X) : ↥X ⧸ L₁.subgroupOf X) = ((⟨y, hyX⟩ : ↥X) : ↥X ⧸ L₁.subgroupOf X) := by
      rw [QuotientGroup.eq, mem_subgroupOf]
      show (x : G)⁻¹ * y ∈ L₁
      rw [hxyz]
      have e2 : (y * z')⁻¹ * y = z'⁻¹ * (y⁻¹ * y) := by group
      rw [e2, inv_mul_cancel, mul_one]
      exact inv_mem hz'L1
    refine ⟨k, ?_⟩
    rw [e, ← QuotientGroup.mk_pow]
    have : (⟨y, hyX⟩ : ↥X) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hyk)
    rw [this, QuotientGroup.mk_one]

  have hTsylX : IsSylowTwoOf T X := A5.isSylowTwoOf_of_le S.h13.sylow hTX
  set T' := (T.subgroupOf X).map (QuotientGroup.mk' (L₁.subgroupOf X)) with hT'
  have hdvd : T'.index ∣ (T.subgroupOf X).index :=
    index_map_dvd _ (QuotientGroup.mk'_surjective _)
  obtain ⟨n, hn⟩ := hQ2.index T'
  have hn0 : n = 0 := by
    by_contra h
    have h2 : 2 ∣ T'.index := by
      rw [hn]
      exact dvd_pow_self 2 h
    exact hTsylX.2.2 (h2.trans hdvd)
  rw [hn0, pow_zero] at hn
  have hTtop : T' = ⊤ := index_eq_one.1 hn
  intro x hx
  have hmem : QuotientGroup.mk' (L₁.subgroupOf X) ⟨x, hx⟩ ∈ T' := by
    rw [hTtop]
    exact mem_top _
  obtain ⟨t, ht, hteq⟩ := hmem
  have h1 := QuotientGroup.eq.1 hteq
  rw [mem_subgroupOf] at h1
  have ht' : (t : G) ∈ T := mem_subgroupOf.1 ht
  have e : x = (t : G) * ((t : G)⁻¹ * x) := by group
  rw [e]
  exact mul_mem (mem_sup_right ht') (mem_sup_left h1)

end CFSG.Quasithin.H13.U3
