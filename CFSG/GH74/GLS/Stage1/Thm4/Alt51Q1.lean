module

public import CFSG.GH74.GLS.Stage1.Thm4.Alt51Cover
public import CFSG.GH74.GLS.Stage1.Thm4.L98c
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Hat
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Basic
public import CFSG.GH74.GLS.Stage1.Thm4.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm4.Alt51

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5
open scoped commutatorElement

section TwoElements

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem eq_one_of_hat_eq_one (a : ↥K) (h : hatMk K a = 1) (h2 : ∃ k : ℕ, a ^ (2 ^ k) = 1) :
    a = 1 := by
  obtain ⟨k, hk⟩ := h2
  have hmem : a ∈ (hatMk K).ker := h
  have hodd := odd_card_ker_hatMk K
  have h1 : orderOf (⟨a, hmem⟩ : (hatMk K).ker) ∣ Nat.card (hatMk K).ker := orderOf_dvd_natCard _
  have h3 : Odd (orderOf (⟨a, hmem⟩ : (hatMk K).ker)) := Odd.of_dvd_nat hodd h1
  have h4 : orderOf (⟨a, hmem⟩ : (hatMk K).ker) = orderOf a := by
    rw [← Subgroup.orderOf_coe (⟨a, hmem⟩ : (hatMk K).ker), ← Subgroup.orderOf_coe a]
  rw [h4] at h3
  have h5 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h6 : Nat.Coprime (orderOf a) (2 ^ k) :=
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 h3)).symm
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h6 h5)

theorem eq_of_hat_eq (a b : ↥K) (hab : hatMk K a = hatMk K b) (ha : ∃ k : ℕ, a ^ (2 ^ k) = 1)
    (hb : ∃ k : ℕ, b ^ (2 ^ k) = 1) (hc : a * b = b * a) : a = b := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨l, hl⟩ := hb
  have hcomm : Commute a b := hc
  have h1 : hatMk K (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
  have h2 : ∃ m : ℕ, (a * b⁻¹) ^ (2 ^ m) = 1 := by
    refine ⟨max k l, ?_⟩
    rw [hcomm.inv_right.mul_pow]
    have e1 : a ^ (2 ^ max k l) = 1 := by
      have : 2 ^ max k l = 2 ^ k * 2 ^ (max k l - k) := by
        rw [← pow_add]; congr 1; omega
      rw [this, pow_mul, hk, one_pow]
    have e2 : b ^ (2 ^ max k l) = 1 := by
      have : 2 ^ max k l = 2 ^ l * 2 ^ (max k l - l) := by
        rw [← pow_add]; congr 1; omega
      rw [this, pow_mul, hl, one_pow]
    rw [inv_pow, e1, e2, inv_one, mul_one]
  exact mul_inv_eq_one.1 (eq_one_of_hat_eq_one _ h1 h2)

end TwoElements


section ZStar

variable {G : Type} [Group G] {K : Subgroup G}

theorem conj_eq_one_iff {H : Type} [Group H] (c : H) : MulAut.conj c = 1 ↔ c ∈ center H := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h g
    have h1 := congrArg (fun f : MulAut H => f g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  · intro h
    ext g
    simp only [MulAut.conj_apply, MulAut.one_apply]
    calc c * g * c⁻¹ = g * c * c⁻¹ := by rw [← h g]
      _ = g := by group

theorem mem_zStar_iff_hat_mem_center (k : ↥K) :
    (k : G) ∈ zStar K ↔ hatMk K k ∈ center (HatT K) := by
  have hkN : (k : G) ∈ normalizer (K : Set G) := Subgroup.le_normalizer k.2
  have h1 : (k : G) ∈ zStar K ↔ (k : G) ∈ cSec K := by
    unfold zStar cSec
    simp [k.2]
  rw [h1, ← phi_eq_one_iff K hkN, phi_of_mem K k.2]
  exact conj_eq_one_iff _

theorem zStar_conj {s : G} (hs : s ∈ normalizer (K : Set G)) {n : G} (hn : n ∈ zStar K) :
    s * n * s⁻¹ ∈ zStar K := by
  have hnK : n ∈ K := hn.1
  have hsnK : s * n * s⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hs n).1 hnK
  have h1 := (mem_zStar_iff_hat_mem_center ⟨n, hnK⟩).1 hn
  have h2 : hatMk K ⟨s * n * s⁻¹, hsnK⟩ = phi K s hs (hatMk K ⟨n, hnK⟩) :=
    (phi_mk K hs ⟨n, hnK⟩).symm
  refine (mem_zStar_iff_hat_mem_center ⟨s * n * s⁻¹, hsnK⟩).2 ?_
  rw [h2]
  rw [Subgroup.mem_center_iff] at h1 ⊢
  intro g
  obtain ⟨g', rfl⟩ := (phi K s hs).surjective g
  rw [← map_mul, ← map_mul, h1 g']

theorem mem_normalizer_zStar {s : G} (hs : s ∈ normalizer (K : Set G)) :
    s ∈ normalizer (zStar K : Set G) := by
  refine Subgroup.mem_normalizer_iff.2 fun m => ⟨fun hm => zStar_conj hs hm, fun hm => ?_⟩
  have := zStar_conj ((normalizer (K : Set G)).inv_mem hs) hm
  simpa [mul_assoc] using this

theorem pPrimeCoreOf_le_zStar : pPrimeCoreOf 2 K ≤ zStar K := by
  intro o ho
  have hoK : o ∈ K := (Subgroup.map_subtype_le _) ho
  have := (mem_zStar_iff_hat_mem_center (K := K) ⟨o, hoK⟩).2
    (by rw [(hatMk_eq_one_iff K ⟨o, hoK⟩).2 ho]; exact one_mem _)
  exact this

theorem z_mem_zStar {z : G} (hKz : K ≤ Cz z) (hz : z ∈ K) : z ∈ zStar K := by
  refine ⟨hz, Subgroup.le_normalizer hz,
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hz), fun k hk => ?_⟩
  have h1 : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.1 (hKz hk)
  have : ⁅k, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h1
  rw [this]
  exact one_mem _

end ZStar


section Rank

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_center_of {H : Type} [Group H] {zh : H} (hzh : zh ∈ center H) {x y : H}
    (h : x * y = y * x ∨ x * y = zh * (y * x)) : ⁅x, y⁆ ∈ center H := by
  rcases h with h | h
  · have : ⁅x, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h
    rw [this]
    exact one_mem _
  · have : ⁅x, y⁆ = zh := by
      calc ⁅x, y⁆ = x * y * x⁻¹ * y⁻¹ := rfl
        _ = zh * (y * x) * x⁻¹ * y⁻¹ := by rw [h]
        _ = zh := by group
    rw [this]
    exact hzh

theorem false_of_Q1_element (hG : CFSG.GH74.Gen4 G) {z : G} (hz2 : orderOf z = 2) {K : Subgroup G}
    (hKz : K ≤ Cz z) (hz : z ∈ K) {n : ℕ} (hn : 8 ≤ n) (hcov : IsDoubleCoverOfAlt (HatT K) n)
    {q : G} (hq : q ∈ cSec K) (hqz : q * z = z * q) (hq2 : IsPGroup 2 (Subgroup.zpowers q))
    (hqnz : q ∉ Subgroup.zpowers z) (hqsq : q * q ∈ Subgroup.zpowers z) : False := by
  classical
  obtain ⟨zh, a, hcen, hzhc, hzh1, hzh2, hasq, hacomm, haind⟩ := exists_Q8Q8 hn hcov
  have hzsq : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
  have hzs : z ∈ zStar K := z_mem_zStar hKz hz
  have hz2K : ∃ k : ℕ, (⟨z, hz⟩ : ↥K) ^ (2 ^ k) = 1 :=
    ⟨1, Subtype.ext (by simpa using hzsq)⟩
  have hzhat : hatMk K ⟨z, hz⟩ = zh := by
    have hc : hatMk K ⟨z, hz⟩ ∈ center (HatT K) :=
      (mem_zStar_iff_hat_mem_center ⟨z, hz⟩).1 hzs
    rcases hcen _ hc with h | h
    · exfalso
      have h1 := eq_one_of_hat_eq_one (⟨z, hz⟩ : ↥K) h hz2K
      have h2 : z = 1 := congrArg Subtype.val h1
      rw [h2, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    · exact h
  choose xk hxk using fun i => hatMk_surjective K (a i)
  let xs : Fin 4 → G := fun i => (xk i : G)
  let x : Fin 5 → G := Fin.snoc (α := fun _ => G) xs q
  have hxlast : x (Fin.last 4) = q := by simp only [x, Fin.snoc_last]
  have hxcast : ∀ i : Fin 4, x i.castSucc = (xk i : G) := fun i => by simp [x, xs]
  have hqN : q ∈ normalizer (K : Set G) := hq.1
  have hcertA : ∀ y : HatT K, y ∈ center (HatT K) → y = 1 ∨ y = zh := hcen
  have hnorm : ∀ i, x i ∈ normalizer (zStar K : Set G) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hxlast]; exact mem_normalizer_zStar hqN
    · rw [hxcast]; exact mem_normalizer_zStar (Subgroup.le_normalizer (xk j).2)
  have hsq : ∀ i, x i ^ 2 ∈ zStar K := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hxlast, pow_two]; exact (Subgroup.zpowers_le.2 hzs) hqsq
    · rw [hxcast]
      have h1 : (xk j : G) ^ 2 = ((xk j ^ 2 : ↥K) : G) := by simp
      rw [h1, mem_zStar_iff_hat_mem_center, map_pow, hxk, pow_two, hasq]
      exact hzhc
  have hcomm : ∀ i j, ⁅x i, x j⁆ ∈ zStar K := by
    intro i j
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · rw [hxlast]; simp [one_mem]
      · rw [hxlast, hxcast]
        have h1 : ⁅(xk j' : G), q⁆ ∈ pPrimeCoreOf 2 K := hq.2.2 _ (xk j').2
        have h2 : ⁅q, (xk j' : G)⁆ = ⁅(xk j' : G), q⁆⁻¹ := (commutatorElement_inv _ _).symm
        rw [h2]
        exact pPrimeCoreOf_le_zStar ((pPrimeCoreOf 2 K).inv_mem h1)
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · rw [hxlast, hxcast]
        exact pPrimeCoreOf_le_zStar (hq.2.2 _ (xk i').2)
      · rw [hxcast, hxcast]
        have h1 : ⁅(xk i' : G), (xk j' : G)⁆ = ((⁅xk i', xk j'⁆ : ↥K) : G) := by
          simp [commutatorElement_def]
        rw [h1, mem_zStar_iff_hat_mem_center]
        have h2 : hatMk K ⁅xk i', xk j'⁆ = ⁅a i', a j'⁆ := by
          rw [map_commutatorElement, hxk, hxk]
        rw [h2]
        exact commutator_mem_center_of hzhc (hacomm i' j')
  have hprod : ∀ c : Fin 5 → Fin 2, (List.ofFn fun i => x i ^ (c i : ℕ)).prod =
      (List.ofFn fun i : Fin 4 => (xk i : G) ^ ((c i.castSucc : Fin 2) : ℕ)).prod *
        q ^ ((c (Fin.last 4) : Fin 2) : ℕ) := by
    intro c
    rw [List.ofFn_succ', List.prod_concat]
    simp only [hxcast, hxlast]
  have hker : ∀ c : Fin 5 → Fin 2, c ≠ 0 → (List.ofFn fun i => x i ^ (c i : ℕ)).prod ∉ zStar K := by
    intro c hc hmem
    rw [hprod c] at hmem
    set c' : Fin 4 → Fin 2 := fun i => c i.castSucc with hc'
    let uk : ↥K := (List.ofFn fun i : Fin 4 => xk i ^ ((c' i : Fin 2) : ℕ)).prod
    have huk : (uk : G) =
        (List.ofFn fun i : Fin 4 => (xk i : G) ^ ((c' i : Fin 2) : ℕ)).prod := by
      have h := map_list_prod K.subtype (List.ofFn fun i : Fin 4 => xk i ^ ((c' i : Fin 2) : ℕ))
      rw [List.map_ofFn] at h
      have e : (K.subtype ∘ fun i : Fin 4 => xk i ^ ((c' i : Fin 2) : ℕ)) =
          fun i => (xk i : G) ^ ((c' i : Fin 2) : ℕ) := by
        funext i
        simp only [Function.comp_apply, map_pow]
        rfl
      rw [e] at h
      exact h
    have hukhat : hatMk K uk = (List.ofFn fun i : Fin 4 => a i ^ ((c' i : Fin 2) : ℕ)).prod := by
      have h := map_list_prod (hatMk K) (List.ofFn fun i : Fin 4 => xk i ^ ((c' i : Fin 2) : ℕ))
      rw [List.map_ofFn] at h
      have e : (hatMk K ∘ fun i : Fin 4 => xk i ^ ((c' i : Fin 2) : ℕ)) =
          fun i => a i ^ ((c' i : Fin 2) : ℕ) := by
        funext i
        simp only [Function.comp_apply, map_pow, hxk]
      rw [e] at h
      exact h
    rw [← huk] at hmem
    by_cases h0 : (c (Fin.last 4) : Fin 2) = 0
    ·
      have hc'0 : c' ≠ 0 := by
        intro h
        apply hc
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · exact h0
        · exact congrFun h j
      rw [h0] at hmem
      simp only [Fin.val_zero, pow_zero, mul_one] at hmem
      have hcent := (mem_zStar_iff_hat_mem_center uk).1 hmem
      rw [hukhat] at hcent
      rcases hcen _ hcent with h | h
      · exact (haind c' hc'0).1 h
      · exact (haind c' hc'0).2 h
    ·
      have h1 : (c (Fin.last 4) : Fin 2) = 1 := by
        have hlt := (c (Fin.last 4)).isLt
        rw [Fin.ext_iff] at h0 ⊢
        simp only [Fin.val_zero, Fin.val_one] at h0 ⊢
        omega
      rw [h1] at hmem
      simp only [Fin.val_one, pow_one] at hmem
      have hqK : q ∈ K := by
        have := K.mul_mem (K.inv_mem uk.2) hmem.1
        simpa using this
      have hq2K : ∃ k : ℕ, (⟨q, hqK⟩ : ↥K) ^ (2 ^ k) = 1 := by
        obtain ⟨k, hk⟩ := hq2 ⟨q, Subgroup.mem_zpowers q⟩
        refine ⟨k, Subtype.ext ?_⟩
        have := congrArg Subtype.val hk
        simpa using this
      have hqzs : q ∈ zStar K := ⟨hqK, hq⟩
      have hcentq := (mem_zStar_iff_hat_mem_center (⟨q, hqK⟩ : ↥K)).1 hqzs
      rcases hcen _ hcentq with h | h
      · have h2 := eq_one_of_hat_eq_one (⟨q, hqK⟩ : ↥K) h hq2K
        have h3 : q = 1 := congrArg Subtype.val h2
        exact hqnz (h3 ▸ one_mem _)
      · have h2 := eq_of_hat_eq (⟨q, hqK⟩ : ↥K) ⟨z, hz⟩ (by rw [h, hzhat]) hq2K hz2K
          (Subtype.ext hqz)
        have h3 : q = z := congrArg Subtype.val h2
        exact hqnz (h3 ▸ Subgroup.mem_zpowers z)
  have hcert := Generic.rankCertified_of_section_involutions (zStar K) x hnorm hsq hcomm hker
    (s := 4) (by norm_num)
  exact hcert.not_gen4 le_rfl hG

end Rank


section Main

theorem exists_q {G : Type} [Group G] {z x : G} {S : Subgroup G} (hS : IsPGroup 2 ↥S) (hxS : x ∈ S)
    (hxz : x ∉ Subgroup.zpowers z) :
    ∃ q ∈ Subgroup.zpowers x, q ∉ Subgroup.zpowers z ∧ q * q ∈ Subgroup.zpowers z := by
  classical
  have h2 : ∃ k : ℕ, x ^ (2 ^ k) ∈ Subgroup.zpowers z := by
    obtain ⟨k, hk⟩ := hS ⟨x, hxS⟩
    refine ⟨k, ?_⟩
    have : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    rw [this]
    exact one_mem _
  have hk : x ^ (2 ^ Nat.find h2) ∈ Subgroup.zpowers z := Nat.find_spec h2
  have hk0 : Nat.find h2 ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hk
    exact hxz hk
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  refine ⟨x ^ (2 ^ m), Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _, ?_, ?_⟩
  · intro hmem
    exact Nat.find_min h2 (by omega : m < Nat.find h2) hmem
  · have : x ^ (2 ^ m) * x ^ (2 ^ m) = x ^ (2 ^ Nat.find h2) := by
      rw [← pow_add, hm, pow_succ]
      congr 1
      omega
    rw [this]
    exact hk

theorem z_mem_sylow {G : Type} [Group G] [Finite G] {z : G} (hz2 : orderOf z = 2) {S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cz z)) : z ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl : M.Syl2In S (Cz z) := (CFSG.ABGLocalTools.isSylowOf_iff).1 hS
  have hzC : z ∈ Cz z := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2]; norm_num)
  obtain ⟨P, hP, hzP⟩ := M.exists_syl2In_ge hzp ((Subgroup.zpowers_le).2 hzC)
  obtain ⟨c, hcC, hc⟩ := M.Syl2In.exists_conj hSyl hP
  have hzP' : z ∈ P := hzP (Subgroup.mem_zpowers z)
  rw [hc, M.mem_cj] at hzP'
  have hcz : c * z * c⁻¹ = z := by
    have : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.1 hcC
    rw [this]
    group
  rwa [hcz] at hzP'

theorem step9_8_q1_thm : Step9_8_Q1 := by
  intro G _ _ Lh _ z t S K hstd _hr1
  obtain ⟨n, hn8, -, hLn⟩ := hstd.cover
  obtain ⟨e⟩ := hstd.K_rigid.2
  have hcov : IsDoubleCoverOfAlt (HatT K) n := isDoubleCoverOfAlt_congr e.symm hLn
  have hKz : K ≤ Cz z := hstd.K_rigid.1.1.2.2.1
  have hz : z ∈ K := hstd.z_mem
  have hz2 : orderOf z = 2 := hstd.z_ord
  have hSsyl : M.Syl2In S (Cz z) := (CFSG.ABGLocalTools.isSylowOf_iff).1 hstd.sylow
  have hSg : IsPGroup 2 ↥S := hSsyl.2.1
  have hSle : S ≤ Cz z := hSsyl.1
  have hzS : z ∈ S := z_mem_sylow hz2 hstd.sylow
  have hzc : z ∈ cSec K := (z_mem_zStar hKz hz).2
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ S ⊓ cSec K := hx
    by_contra hxz
    obtain ⟨q, hqx, hqz, hqsq⟩ := exists_q hSg hx'.1 hxz
    have hzpS : Subgroup.zpowers x ≤ S := (Subgroup.zpowers_le).2 hx'.1
    have hzpc : Subgroup.zpowers x ≤ cSec K := (Subgroup.zpowers_le).2 hx'.2
    have hqS : q ∈ S := hzpS hqx
    have hqcomm : q * z = z * q := Subgroup.mem_centralizer_singleton_iff.1 (hSle hqS)
    have hqpg : IsPGroup 2 ↥(Subgroup.zpowers q) :=
      hSg.to_le ((Subgroup.zpowers_le).2 hqS)
    exact false_of_Q1_element hstd.std.gen4 hz2 hKz hz hn8 hcov (hzpc hqx) hqcomm hqpg hqz hqsq
  · exact (Subgroup.zpowers_le).2 ⟨hzS, hzc⟩

end Main

end CFSG.GH74.GLS.Stage1.Thm4.Alt51
