module

public import CFSG.Goldschmidt.Steps.G3bPSL2
public import CFSG.Walter.Bender1970.S2.Basic
public import CFSG.StronglyEmbedded.Catalog
public import CFSG.Walter.PSL2Facts.OddMaximal

public section

namespace CFSG.Goldschmidt.G3b

open CFSG.Walter CFSG.GorensteinWalter
open scoped MatrixGroups

theorem normal_sylow_of_mulEquiv {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {p : ℕ} [Fact p.Prime] (e : G ≃* H) (hH : Subsingleton (Sylow p H)) (P : Sylow p G) :
    (P : Subgroup G).Normal := by
  have hs : Function.Surjective e.toMonoidHom := e.surjective
  have : Subsingleton (Sylow p G) := ⟨fun P Q => by
    have h := Subsingleton.elim (P.mapSurjective hs) (Q.mapSurjective hs)
    have h' : ((P.mapSurjective hs : Sylow p H) : Subgroup H) =
        ((Q.mapSurjective hs : Sylow p H) : Subgroup H) := by
      rw [h]
    rw [Sylow.coe_mapSurjective, Sylow.coe_mapSurjective] at h'
    exact Sylow.ext (Subgroup.map_injective e.injective h')⟩
  exact Sylow.normal_of_subsingleton P

section L2

variable {L : Type*} [Group L] [Finite L] {p f : ℕ} [Fact p.Prime]

theorem sylow_isKleinFour_of_mulEquiv (e : L ≃* PSL(2, GaloisField p f)) (hp : Odd p)
    (hf : 0 < f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) (S : Sylow 2 L) :
    IsKleinFour (S : Subgroup L) := by
  let S' : Sylow 2 PSL(2, GaloisField p f) := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS' : (S' : Subgroup PSL(2, GaloisField p f)) = (S : Subgroup L).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  have hK := psl2_odd_sylow_two_isKleinFour hp hf h8 S'
  rw [hS'] at hK
  exact isKleinFour_of_mulEquiv' (e.subgroupMap (S : Subgroup L)).symm hK

theorem centralizer_sylow_of_mulEquiv
    (e : L ≃* PSL(2, GaloisField p f)) (hp : Odd p)
    (hf : 0 < f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) (S : Sylow 2 L) :
    Subgroup.centralizer ((S : Subgroup L) : Set L) = S := by
  have hK := sylow_isKleinFour_of_mulEquiv e hp hf h8 S
  have hKm : IsKleinFour ((S : Subgroup L).map e.toMonoidHom) :=
    isKleinFour_of_mulEquiv' (e.subgroupMap (S : Subgroup L)) hK
  have h := psl2_centralizer_kleinFour (GaloisField p f)
    (isOddPrimePower_of_card (GaloisField.card p f hf.ne') hp hf) _ hKm
  rw [Subgroup.coe_map, MulEquiv.coe_toMonoidHom, ← map_centralizer_mulEquiv] at h
  exact Subgroup.map_injective e.injective h

omit [Finite L] in
theorem isConj_of_mulEquiv' (e : L ≃* PSL(2, GaloisField p f)) (hp : Odd p) (hf : 0 < f) :
    ∀ x y : L, orderOf x = 2 → orderOf y = 2 → IsConj x y := by
  intro x y hx hy
  have h := psl2_odd_isConj_of_orderOf_eq_two hp hf (x := e x) (y := e y)
    (by rwa [MulEquiv.orderOf_eq]) (by rwa [MulEquiv.orderOf_eq])
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine isConj_iff.mpr ⟨e.symm c, e.injective ?_⟩
  simpa using hc

theorem normalizer_sylow_mulEquiv_of_mulEquiv
    (e : L ≃* PSL(2, GaloisField p f)) (hp : Odd p)
    (hf : 0 < f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) (S : Sylow 2 L) :
    Nonempty (Subgroup.normalizer ((S : Subgroup L) : Set L) ≃* alternatingGroup (Fin 4)) :=
  normalizer_mulEquiv_alternatingGroup_four S (sylow_isKleinFour_of_mulEquiv e hp hf h8 S)
    (centralizer_sylow_of_mulEquiv e hp hf h8 S) (isConj_of_mulEquiv' e hp hf)

noncomputable def centralizerEquiv {M : Type*} [Group M] (e : L ≃* M) (a : L) :
    Subgroup.centralizer ({a} : Set L) ≃* Subgroup.centralizer ({e a} : Set M) :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_centralizer_singleton_mulEquiv e a))

omit [Finite L] in
theorem centralizer_dihedral_of_mulEquiv (e : L ≃* PSL(2, GaloisField p f)) (hp : Odd p)
    (hf : 0 < f) {a : L} (ha : orderOf a = 2) :
    (p ^ f % 4 = 1 →
      Nonempty (Subgroup.centralizer ({a} : Set L) ≃* DihedralGroup ((p ^ f - 1) / 2))) ∧
    (p ^ f % 4 = 3 →
      Nonempty (Subgroup.centralizer ({a} : Set L) ≃* DihedralGroup ((p ^ f + 1) / 2))) := by
  obtain ⟨h1, h3⟩ := psl2_odd_centralizer_involution hp hf (t := e a)
    (by rwa [MulEquiv.orderOf_eq])
  exact ⟨fun h => ⟨(centralizerEquiv e a).trans (Classical.choice (h1 h).2)⟩,
    fun h => ⟨(centralizerEquiv e a).trans (Classical.choice (h3 h).2)⟩⟩

omit [Finite L] in
theorem centralizer_isCoatom_of_mulEquiv
    (e : L ≃* PSL(2, GaloisField p f)) (hp : Odd p)
    (hf : 0 < f) (h11 : 11 ≤ p ^ f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) {a : L}
    (ha : orderOf a = 2) : IsCoatom (Subgroup.centralizer ({a} : Set L)) := by
  have h := psl2_odd_centralizer_involution_isCoatom hp hf h11 h8 (t := e a)
    (by rwa [MulEquiv.orderOf_eq])
  rw [← map_centralizer_singleton_mulEquiv e a, ← MulEquiv.coe_mapSubgroup] at h
  exact (OrderIso.isCoatom_iff _ _).mp h

theorem card_alternatingGroup_four' : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem five_facts_of_mulEquiv
    [IsSimpleGroup L] (e : L ≃* PSL(2, GaloisField p f))
    (hp : Odd p) (hf : 0 < f) (hq : p ^ f = 5) (S : Sylow 2 L) {a : L}
    (haS : a ∈ (S : Subgroup L)) (ha1 : a ≠ 1) :
    Nonempty (L ≃* alternatingGroup (Fin 5)) ∧
      IsCoatom (Subgroup.normalizer ((S : Subgroup L) : Set L)) ∧
      ∀ M : Subgroup L, IsCoatom M → Subgroup.centralizer ({a} : Set L) ≤ M →
        M = Subgroup.normalizer ((S : Subgroup L) : Set L) := by
  classical
  set F := GaloisField p f
  set Sg := (S : Subgroup L) with hSg
  set N := Subgroup.normalizer (Sg : Set L) with hN
  have hpp : p.Prime := Fact.out
  have hp5 : p = 5 := by
    have h5 : p ∣ 5 := hq ▸ dvd_pow_self p hf.ne'
    exact (Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).mp h5
  subst hp5
  have hf1 : f = 1 := by
    have h : 5 ^ f = 5 ^ 1 := by rw [hq, pow_one]
    exact Nat.pow_right_injective (by norm_num) h
  subst hf1
  have h8 : 5 ^ 1 % 8 = 3 ∨ 5 ^ 1 % 8 = 5 := by norm_num
  have hF : Nat.card F = 5 ^ 1 := GaloisField.card 5 1 one_ne_zero
  have hF' : IsOddPrimePower (Nat.card F) := isOddPrimePower_of_card hF hp hf
  have hcardL : Nat.card L = 60 := by
    rw [Nat.card_congr e.toEquiv, psl2_card_formula F hF', hF]
    norm_num
  have hKS := sylow_isKleinFour_of_mulEquiv e hp hf h8 S
  have hS4 : Nat.card Sg = 4 := hKS.card_four
  have hSN : Sg ≤ N := Subgroup.le_normalizer
  obtain ⟨eN⟩ := normalizer_sylow_mulEquiv_of_mulEquiv e hp hf h8 S
  have hN12 : Nat.card N = 12 := by
    rw [Nat.card_congr eN.toEquiv, card_alternatingGroup_four']
  have hNtop : N ≠ ⊤ := by
    intro h
    have := congrArg (fun H : Subgroup L => Nat.card H) h
    simp only [Subgroup.card_top] at this
    omega
  have hNcoatom : IsCoatom N := by
    refine ⟨hNtop, fun K hNK => ?_⟩
    have hdvd : 12 ∣ Nat.card K := hN12 ▸ Subgroup.card_dvd_of_le hNK.le
    have hlt : 12 < Nat.card K := hN12 ▸ Subgroup.card_lt_of_lt hNK
    have hK60 : Nat.card K ∣ 60 := hcardL ▸ Subgroup.card_subgroup_dvd_card K
    apply Subgroup.eq_top_of_card_eq
    rw [hcardL]
    obtain ⟨m, hm⟩ := hdvd
    rw [hm] at hlt hK60 ⊢
    have hm5 : m ∣ 5 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 12) (by simpa using hK60)
    have hm' : m ≤ 5 := Nat.le_of_dvd (by norm_num) hm5
    interval_cases m <;> simp_all
  have ha2 : orderOf a = 2 := orderOf_eq_two_of_kleinFour hKS haS ha1
  have hCa : Subgroup.centralizer ({a} : Set L) = Sg := by
    have hcard : Nat.card (Subgroup.centralizer ({a} : Set L)) = 4 := by
      obtain ⟨h1, -⟩ := psl2_odd_centralizer_involution hp hf (t := e a)
        (by rwa [MulEquiv.orderOf_eq])
      rw [Nat.card_congr (centralizerEquiv e a).toEquiv, (h1 (by norm_num)).1]
      norm_num
    have hle : Sg ≤ Subgroup.centralizer ({a} : Set L) := by
      have : IsMulCommutative Sg := @IsKleinFour.isMulCommutative _ _ hKS
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : Sg) ⟨a, haS⟩)
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hS4])).symm
  refine ⟨CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five hcardL, hNcoatom, ?_⟩
  intro M hM hCM
  rw [hCa] at hCM
  have hMN : M ≤ N := by
    have hM4 : 4 ∣ Nat.card M := hS4 ▸ Subgroup.card_dvd_of_le hCM
    have hMlt : Nat.card M < 60 := by
      have := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hM.1)
      rwa [Subgroup.card_top, hcardL] at this
    have hMne4 : Nat.card M ≠ 4 := by
      intro h4
      have hMS : M = Sg := (Subgroup.eq_of_le_of_card_ge hCM (by rw [h4, hS4])).symm
      have hSN' : Sg < N := by
        refine lt_of_le_of_ne hSN fun h => ?_
        have := congrArg (fun H : Subgroup L => Nat.card H) h
        omega
      rw [hMS] at hM
      exact hNtop (hM.2 N hSN')
    set M' := M.map e.toMonoidHom with hM'
    have hM'card : Nat.card M' = Nat.card M :=
      Nat.card_congr (e.subgroupMap M).toEquiv.symm
    have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 := by rw [hF]; norm_num
    rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hF M' with
      hEl | ⟨z, hz, hzc, -⟩ | ⟨z, hz, hzc, -⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨h16, -⟩ | ⟨-, ⟨eA5⟩⟩ |
        ⟨m, t, -, ht, NB, CB, hNB, -, hNBcard, -, hCBcard, hdisj, hsup⟩ |
        ⟨m, hm, hmf, ⟨eP⟩⟩ | ⟨m, hm0, hmf, -⟩
    ·
      obtain ⟨k, hk⟩ := (haveI := hEl; IsElementaryAbelian.isPGroup 5 M').exists_card_eq
      rw [hM'card] at hk
      rw [hk] at hM4
      have : (2 : ℕ) ∣ 5 := Nat.prime_two.dvd_of_dvd_pow (dvd_trans (by norm_num) hM4)
      omega
    ·
      rw [hgcd, hF] at hz
      rw [hM'card] at hzc
      have hz0 : 0 < z := hzc ▸ Nat.card_pos
      have hzle : z ≤ 3 := by
        rcases hz with hz | hz
        · exact (Nat.le_of_dvd (by norm_num) hz).trans (by norm_num)
        · exact Nat.le_of_dvd (by norm_num) hz
      rw [hzc] at hM4
      have := Nat.le_of_dvd hz0 hM4
      omega
    ·
      rw [hgcd, hF] at hz
      rw [hM'card] at hzc
      have hzle : z ≤ 3 := by
        rcases hz with hz | hz
        · exact (Nat.le_of_dvd (by norm_num) hz).trans (by norm_num)
        · exact Nat.le_of_dvd (by norm_num) hz
      rw [hzc] at hM4 hMne4
      have hz0 : 0 < z := by
        rcases Nat.eq_zero_or_pos z with h | h
        · rw [h] at hzc
          exact absurd hzc (Nat.card_pos (α := M)).ne'
        · exact h
      interval_cases z <;> omega
    ·
      let eMA : M ≃* alternatingGroup (Fin 4) := (e.subgroupMap M).trans eA4
      have hM12 : Nat.card M = 12 := by
        rw [Nat.card_congr eMA.toEquiv, card_alternatingGroup_four']
      have hSMp : IsPGroup 2 (Sg.subgroupOf M) := by
        refine IsPGroup.of_card (n := 2) ?_
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCM).toEquiv, hS4]
        norm_num
      have hSMidx : ¬ 2 ∣ (Sg.subgroupOf M).index := by
        have h := (Sg.subgroupOf M).card_mul_index
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCM).toEquiv, hS4, hM12] at h
        omega
      have hsub : Subsingleton (Sylow 2 (alternatingGroup (Fin 4))) :=
        alternatingGroup.subsingleton_two_sylow (by simp)
      have hnorm := normal_sylow_of_mulEquiv eMA hsub (hSMp.toSylow hSMidx)
      rw [IsPGroup.toSylow_coe] at hnorm
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hCM).mp hnorm
    ·
      norm_num at h16
    ·
      have h60 : Nat.card M = 60 := by
        rw [← hM'card, Nat.card_congr eA5.toEquiv]
        exact (Nat.card_eq_fintype_card).trans rfl
      omega
    ·
      have hcompl : NB.IsComplement' CB :=
        Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
          (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
      have hc : Nat.card M' = 5 ^ m * t := by
        rw [← hcompl.card_mul_card, hNBcard, hCBcard]
      rw [hM'card] at hc
      rw [hc] at hM4
      have ht2 : t ∣ 2 := by simpa using ht
      have h4t : 4 ∣ t := by
        have hcop : Nat.Coprime 4 (5 ^ m) := Nat.Coprime.pow_right m (by norm_num)
        exact hcop.dvd_of_dvd_mul_left hM4
      have := Nat.le_of_dvd (by norm_num) (dvd_trans h4t ht2)
      omega
    ·
      have hm1 : m = 1 := Nat.eq_one_of_dvd_one hmf
      subst hm1
      have h60 : Nat.card M = 60 := by
        rw [← hM'card, Nat.card_congr eP.toEquiv, psl2_card_formula _
          (isOddPrimePower_of_card (GaloisField.card 5 1 one_ne_zero) hp hf),
          GaloisField.card 5 1 one_ne_zero]
        norm_num
      omega
    ·
      have := Nat.le_of_dvd one_pos hmf
      omega
  rcases hM.le_iff.mp hMN with h | h
  · exact absurd h hNtop
  · exact h.symm

end L2

end CFSG.Goldschmidt.G3b
