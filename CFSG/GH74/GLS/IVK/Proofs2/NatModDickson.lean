module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open BenderSuzuki.MatrixGroups

section Arith

private theorem le_of_pow_dvd_sl2_card {p n m : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hdvd : p ^ m ∣ p ^ n * ((p ^ n) ^ 2 - 1)) : m ≤ n := by
  have hcop : Nat.Coprime (p ^ m) ((p ^ n) ^ 2 - 1) := by
    apply Nat.Coprime.pow_left
    rw [hp.coprime_iff_not_dvd]
    intro h
    have h1 : p ∣ (p ^ n) ^ 2 := Dvd.dvd.pow (dvd_pow_self p hn.ne') two_ne_zero
    have h2 : p ∣ (p ^ n) ^ 2 - ((p ^ n) ^ 2 - 1) := Nat.dvd_sub h1 h
    have h3 : (p ^ n) ^ 2 - ((p ^ n) ^ 2 - 1) = 1 := by
      have : 1 ≤ (p ^ n) ^ 2 := Nat.one_le_pow _ _ (pow_pos hp.pos _)
      omega
    rw [h3] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp (hcop.dvd_of_dvd_mul_right hdvd)

private theorem eq_of_semidirect_card {p n m t s : ℕ} (hp : p.Prime) (hn : 0 < n) (hmn : m ≤ n)
    (htm : t ∣ p ^ m - 1) (htn : t ∣ p ^ n - 1) (hs : s = p ^ m * t) (hge : p ^ n ≤ s) :
    m = n := by
  by_contra hne
  have hlt : m < n := lt_of_le_of_ne hmn hne
  have htg : t ∣ p ^ (Nat.gcd m n) - 1 := by
    have := Nat.dvd_gcd htm htn
    rwa [Nat.pow_sub_one_gcd_pow_sub_one] at this
  have hgpos : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_right _ hn
  have hmg : m + Nat.gcd m n ≤ n := by
    rcases Nat.eq_zero_or_pos m with h0 | hm
    · rw [h0, Nat.gcd_zero_left]
      omega
    · have h1 : Nat.gcd m n ∣ n - m :=
        Nat.dvd_sub (Nat.gcd_dvd_right m n) (Nat.gcd_dvd_left m n)
      have := Nat.le_of_dvd (by omega) h1
      omega
  have hpg : 1 < p ^ (Nat.gcd m n) := Nat.one_lt_pow hgpos.ne' hp.one_lt
  have ht : t < p ^ (Nat.gcd m n) :=
    lt_of_le_of_lt (Nat.le_of_dvd (by omega) htg) (by omega)
  have : s < p ^ n := calc
    s = p ^ m * t := hs
    _ < p ^ m * p ^ (Nat.gcd m n) := Nat.mul_lt_mul_of_pos_left ht (pow_pos hp.pos m)
    _ = p ^ (m + Nat.gcd m n) := (pow_add _ _ _).symm
    _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hmg
  omega

private theorem two_dvd_psl_order_aux {q : ℕ} (hq : Odd q) : 2 ∣ q * (q ^ 2 - 1) / 2 := by
  obtain ⟨k, rfl⟩ := hq
  have h1 : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
    have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    omega
  rw [h1, show (2 * k + 1) * (4 * (k * (k + 1))) =
      2 * (2 * ((2 * k + 1) * (k * (k + 1)))) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  exact dvd_mul_right 2 _

private theorem two_dvd_pgl_order_aux {q : ℕ} (hq : Odd q) : 2 ∣ q * (q ^ 2 - 1) := by
  obtain ⟨k, rfl⟩ := hq
  have h1 : (2 * k + 1) ^ 2 - 1 = 2 * (2 * (k * (k + 1))) := by
    have : (2 * k + 1) ^ 2 = 2 * (2 * (k * (k + 1))) + 1 := by ring
    omega
  rw [h1]
  exact Dvd.dvd.mul_left (dvd_mul_right 2 _) _

end Arith

section Orders

private theorem card_alternatingGroup_four' : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

private theorem card_perm_four' : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

private theorem card_alternatingGroup_five' : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

private theorem two_dvd_card_psl2_galoisField {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hm : m ≠ 0) :
    2 ∣ Nat.card (PSL2MatrixGroup (GaloisField p m)) := by
  have hq : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hform := GorensteinWalter.psl2_card_formula (GaloisField p m)
    ⟨p, m, Fact.out, hpodd, Nat.pos_of_ne_zero hm, hq⟩
  change 2 ∣ Nat.card (GorensteinWalter.PSL2 (GaloisField p m))
  rw [hform, hq]
  exact two_dvd_psl_order_aux hpodd.pow

private theorem two_dvd_card_pgl2_galoisField {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hm : m ≠ 0) :
    2 ∣ Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) := by
  have hq : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hform := GorensteinWalter.pgl2_card_formula (GaloisField p m)
  change 2 ∣ Nat.card (GorensteinWalter.PGL2 (GaloisField p m))
  rw [hform, hq]
  exact two_dvd_pgl_order_aux hpodd.pow

end Orders

section Embedding

variable {F : Type} [Field F]

private theorem sq_eq_one_of_mem_center (s : Matrix.SpecialLinearGroup (Fin 2) F)
    (hs : s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) : s ^ 2 = 1 := by
  obtain ⟨r, hr, hrs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hs
  rw [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrs, ← map_pow, hr, map_one,
    Matrix.SpecialLinearGroup.coe_one]

private theorem injective_mk_comp_subtype [Finite F]
    (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) (hodd : Odd (Nat.card S)) :
    Function.Injective
      ((QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp
        S.subtype) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxc : (x : Matrix.SpecialLinearGroup (Fin 2) F) ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    simpa using hx
  have h2 : x ^ 2 = 1 := Subtype.ext (sq_eq_one_of_mem_center _ hxc)
  obtain ⟨k, hk⟩ := hodd
  have hx1 : x ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_card_eq_one'
  rwa [pow_succ, pow_mul, h2, one_pow, one_mul] at hx1

private theorem exists_subgroup_card_of_le_range {G K : Type*} [Group G] [Group K]
    (S : Subgroup G) (φ : S →* K) (hφ : Function.Injective φ) (N : Subgroup K)
    (hN : N ≤ φ.range) :
    ∃ P : Subgroup G, P ≤ S ∧ Nat.card P = Nat.card N := by
  refine ⟨(N.comap φ).map S.subtype, Subgroup.map_subtype_le _, ?_⟩
  rw [Subgroup.card_map_of_injective S.subtype_injective]
  have h := Subgroup.card_map_of_injective hφ (K := N.comap φ)
  rw [Subgroup.map_comap_eq_self hN] at h
  exact h.symm

private theorem le_of_card_subgroup_psl2 [Finite F] {p n m : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hF : Nat.card F = p ^ n) (N : Subgroup (PSL2MatrixGroup F)) (hN : Nat.card N = p ^ m) :
    m ≤ n := by
  refine le_of_pow_dvd_sl2_card hp hn ?_
  have h1 : Nat.card N ∣ Nat.card (PSL2MatrixGroup F) := Subgroup.card_subgroup_dvd_card N
  have h2 : Nat.card (PSL2MatrixGroup F) ∣
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    change Nat.card (Matrix.SpecialLinearGroup (Fin 2) F ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) ∣ _
    rw [← Subgroup.index_eq_card]
    exact Subgroup.index_dvd_card _
  have h3 := GorensteinWalter.sl2_card_formula F
  rw [hF] at h3
  rw [← hN, ← h3]
  exact h1.trans h2

end Embedding

theorem exists_subgroup_card_eq_of_odd_card_ge
    {F : Type} [Field F] [Finite F] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ n)
    (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (hodd : Odd (Nat.card S)) (hge : Nat.card F ≤ Nat.card S) :
    ∃ P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F), P ≤ S ∧ Nat.card P = Nat.card F := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      have := Finite.one_lt_card (α := F)
      rw [hF, h0] at this
      simp at this
    · exact h0
  have hpnodd : Odd (p ^ n) := (hp.odd_of_ne_two hp2).pow
  have hqodd : Odd (Nat.card F) := by rw [hF]; exact hpnodd
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 :=
    Nat.gcd_eq_right (by obtain ⟨k, hk⟩ := hqodd; omega)
  have hgcd' : Nat.gcd (p ^ n - 1) 2 = 2 := by rw [← hF]; exact hgcd
  let φ : S →* PSL2MatrixGroup F :=
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp S.subtype
  have hinj : Function.Injective φ := injective_mk_comp_subtype S hodd
  let H : Subgroup (PSL2MatrixGroup F) := φ.range
  have eH : S ≃* H := MonoidHom.ofInjective hinj
  have hHS : Nat.card H = Nat.card S := (Nat.card_congr eH.toEquiv).symm
  have hHodd : Odd (Nat.card H) := hHS ▸ hodd
  have hHge : Nat.card F ≤ Nat.card H := hHS ▸ hge
  have hq3 : 3 ≤ Nat.card F := by
    have := Finite.one_lt_card (α := F)
    obtain ⟨k, hk⟩ := hqodd
    omega
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hF H with
    hel | ⟨z, hz, hcard, -⟩ | ⟨z, -, hcard, -⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, htm, htq, N, C, hNn, -, hNcard, -, hCcard, hdisj, hsup⟩ | ⟨m, hm, -, ⟨e⟩⟩ |
      ⟨m, hm, -, ⟨e⟩⟩
  ·
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup p H).exists_card_eq
    have hkn : k ≤ n := le_of_card_subgroup_psl2 hp hn hF H hk
    have h1 : Nat.card H ≤ Nat.card F := by
      rw [hk, hF]
      exact Nat.pow_le_pow_right hp.pos hkn
    exact ⟨S, le_rfl, by omega⟩
  ·
    exfalso
    rw [hgcd] at hz
    rcases hz with hz | hz
    · have := Nat.le_of_dvd (by omega) hz
      omega
    · have := Nat.le_of_dvd (by omega) hz
      omega
  ·
    exfalso
    rw [hcard] at hHodd
    obtain ⟨k, hk⟩ := hHodd
    omega
  ·
    exfalso
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_four'] at hHodd
    exact absurd hHodd (by decide)
  ·
    exfalso
    rw [Nat.card_congr e.toEquiv, card_perm_four'] at hHodd
    exact absurd hHodd (by decide)
  ·
    exfalso
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_five'] at hHodd
    exact absurd hHodd (by decide)
  ·
    have hNC : Nat.card H = p ^ m * t := by
      have hle : C ≤ Subgroup.normalizer (N : Set H) := by
        have := hNn
        rw [Subgroup.normalizer_eq_top]
        exact le_top
      have := GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer N C hle hdisj
      rw [hsup, Subgroup.card_top, hNcard, hCcard] at this
      exact this
    have hN' : Nat.card (N.map H.subtype) = p ^ m := by
      rw [Subgroup.card_map_of_injective H.subtype_injective, hNcard]
    have hmn : m ≤ n := le_of_card_subgroup_psl2 hp hn hF _ hN'
    have htn : t ∣ p ^ n - 1 := by
      rw [hgcd'] at htq
      exact htq.trans (Nat.div_dvd_of_dvd (by obtain ⟨k, hk⟩ := hpnodd; omega))
    have hmeq : m = n :=
      eq_of_semidirect_card hp hn hmn htm htn hNC (by rw [← hF]; exact hHge)
    obtain ⟨P, hPS, hPcard⟩ :=
      exists_subgroup_card_of_le_range S φ hinj (N.map H.subtype) (Subgroup.map_subtype_le N)
    exact ⟨P, hPS, by rw [hPcard, hN', hmeq, hF]⟩
  ·
    exfalso
    have h2 := two_dvd_card_psl2_galoisField (p := p) hp2 hm
    rw [← Nat.card_congr e.toEquiv] at h2
    obtain ⟨k, hk⟩ := hHodd
    omega
  ·
    exfalso
    have h2 := two_dvd_card_pgl2_galoisField (p := p) hp2 hm
    rw [← Nat.card_congr e.toEquiv] at h2
    obtain ⟨k, hk⟩ := hHodd
    omega

end CFSG.GH74.GLS.IVK.Proofs2
