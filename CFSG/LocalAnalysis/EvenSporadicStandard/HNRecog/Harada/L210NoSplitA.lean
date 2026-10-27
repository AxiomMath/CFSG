module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L28Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210Gaschutz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210WrBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210WrElem

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

variable {X : Type} [Group X] [Finite X] {A : Subgroup X} {w : X}
  {ψ : ↥(normalizer (A : Set X)) →* A5WrTwo}

private theorem l210A_natCard_subgroupOf {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

private theorem l210A_isPGroup_two_of_sq_eq_one {G : Type*} [Group G] {E : Subgroup G}
    (h : ∀ x ∈ E, x ^ 2 = 1) : IsPGroup 2 E := by
  rw [isPGroup_iff_orderOf_dvd_pow]
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one, orderOf_dvd_iff_pow_eq_one]
  exact Subtype.ext (by simpa using h (g : G) g.2)

private theorem l210A_factorization_two_pow_mul_odd (a b : ℕ) (hb : b % 2 = 1) :
    (2 ^ a * b).factorization 2 = a := by
  have hb0 : b ≠ 0 := by omega
  rw [Nat.factorization_mul (pow_ne_zero a (by norm_num)) hb0, Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by omega)]
  simp

theorem L210_exists_base_complement (h : L28Hyp A w ψ) {D : Subgroup X}
    (hD : D ≤ normalizer (A : Set X)) (hDe : IsElemAbelian 2 D) (hDA : D ⊓ A = ⊥)
    (h8 : 8 < Nat.card D) :
    ∃ C : Subgroup ↥(normalizer (A : Set X)), C ⊓ ψ.ker = ⊥ ∧ C.map ψ = commutator A5WrTwo := by
  let N : Subgroup X := normalizer (A : Set X)
  let K : Subgroup N := A.subgroupOf N
  let D' : Subgroup N := D.subgroupOf N
  let base : Subgroup A5WrTwo := commutator A5WrTwo
  have hkerK : ψ.ker = K := h.ker
  haveI hAcomm : IsMulCommutative A := h.elemAb.1
  haveI hDcomm : IsMulCommutative D := hDe.1
  haveI hKcomm : IsMulCommutative K := inferInstance
  haveI hKN : K.Normal := inferInstance
  have hKcard : Nat.card K = 256 := by
    change Nat.card (A.subgroupOf N) = 256
    rw [l210A_natCard_subgroupOf (Subgroup.le_normalizer : A ≤ N), h.card]
    norm_num
  have hD'card : Nat.card D' = Nat.card D := by
    change Nat.card (D.subgroupOf N) = Nat.card D
    exact l210A_natCard_subgroupOf hD
  have hKD' : K ⊓ D' = ⊥ := by
    have h1 : K ⊓ D' = (A ⊓ D).subgroupOf N := by
      change (A.subgroupOf N) ⊓ (D.subgroupOf N) = (A ⊓ D).subgroupOf N
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [h1, inf_comm, hDA, Subgroup.bot_subgroupOf]
  let φ : D' →* A5WrTwo := ψ.comp D'.subtype
  have hkerφ : φ.ker = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun d hd => ?_
    have hdK : (d : N) ∈ K := by
      rw [← hkerK, MonoidHom.mem_ker]
      exact MonoidHom.mem_ker.mp hd
    have hdD : (d : N) ∈ D' := d.2
    have hmem : (d : N) ∈ K ⊓ D' := ⟨hdK, hdD⟩
    rw [hKD', Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerφ
  let E : Subgroup A5WrTwo := φ.range
  have hEcard : Nat.card E = Nat.card D' := by
    change Nat.card φ.range = Nat.card D'
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (K := ⊤) hinj,
      Subgroup.card_top]
  have hE : IsElemAbelian 2 E := by
    constructor
    · change IsMulCommutative φ.range
      infer_instance
    · intro x hx
      rw [MonoidHom.mem_range] at hx
      obtain ⟨d, rfl⟩ := hx
      have hd2 : d ^ 2 = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        simpa using hDe.2 (d.1 : X) d.2
      rw [← map_pow, hd2, map_one]
  have hE8 : 8 < Nat.card E := by rw [hEcard, hD'card]; exact h8
  have h16D : Nat.card D ≤ 16 := by
    have h16E := L210_card_le_sixteen_of_isElemAbelian hE
    rwa [hEcard, hD'card] at h16E
  have hEle : E ≤ base := L210_le_base_of_eight_lt_card hE hE8
  have hD2 : IsPGroup 2 D := l210A_isPGroup_two_of_sq_eq_one hDe.2
  obtain ⟨k, hk⟩ := hD2.exists_card_eq
  have hk_le : k ≤ 4 := by
    have hpow : 2 ^ k ≤ 2 ^ 4 := by
      rw [← hk, show (2 : ℕ) ^ 4 = 16 by norm_num]
      exact h16D
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow
  have hk_gt : 3 < k := by
    have hpow : 2 ^ 3 < 2 ^ k := by
      rw [← hk, show (2 : ℕ) ^ 3 = 8 by norm_num]
      exact h8
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow
  have hD16 : Nat.card D = 16 := by
    rw [hk, show k = 4 by omega]
    norm_num
  let N' : Subgroup N := base.comap ψ
  have hmapN' : N'.map ψ = base := by
    change (base.comap ψ).map ψ = base
    exact Subgroup.map_comap_eq_self_of_surjective h.surj base
  have hKN' : K ≤ N' := by
    intro k hk
    show ψ k ∈ base
    have hk1 : ψ k = 1 := by
      rw [← hkerK, MonoidHom.mem_ker] at hk
      exact hk
    rw [hk1]
    exact Subgroup.one_mem base
  have hD'N' : D' ≤ N' := by
    intro d hd
    show ψ d ∈ base
    exact hEle (MonoidHom.mem_range.mpr ⟨⟨d, hd⟩, rfl⟩)
  let K' : Subgroup N' := K.subgroupOf N'
  let D'' : Subgroup N' := D'.subgroupOf N'
  have hK'D'' : K' ⊓ D'' = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨hxK, hxD⟩ := Subgroup.mem_inf.mp hx
    have hmem : (x : N) ∈ K ⊓ D' := ⟨hxK, hxD⟩
    rw [hKD', Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  haveI hK'norm : K'.Normal := inferInstance
  haveI hK'comm : IsMulCommutative K' := inferInstance
  have hK'card : Nat.card K' = 2 ^ 8 := by
    change Nat.card (K.subgroupOf N') = 2 ^ 8
    rw [l210A_natCard_subgroupOf hKN', hKcard]
    norm_num
  have hD''card : Nat.card D'' = 2 ^ 4 := by
    change Nat.card (D'.subgroupOf N') = 2 ^ 4
    rw [l210A_natCard_subgroupOf hD'N', hD'card, hD16]
    norm_num
  have hK'pg : IsPGroup 2 K' := IsPGroup.of_card (n := 8) hK'card
  have hD''pg : IsPGroup 2 D'' := IsPGroup.of_card (n := 4) hD''card
  have hNcard : Nat.card N = 256 * 7200 := by
    have hh := Subgroup.card_ker_mul_card_of_surjective (f := ψ) h.surj
    rw [hkerK, hKcard, L210_card_a5WrTwo] at hh
    exact hh.symm
  have hbaseidx : base.index = 2 := by
    have hbasecard : Nat.card base = 3600 := L210_card_base
    have hh := Subgroup.card_mul_index (H := base)
    rw [hbasecard, L210_card_a5WrTwo] at hh
    omega
  have hN'idx : N'.index = 2 := by
    change (base.comap ψ).index = 2
    have h := Subgroup.index_comap_of_surjective (H := base) (f := ψ) h.surj
    rw [h, hbaseidx]
  have hN'card : Nat.card N' * 2 = Nat.card N := by
    have hh := Subgroup.card_mul_index (H := N')
    rw [hN'idx] at hh
    exact hh
  have hN'card' : Nat.card N' = 256 * 3600 := by
    have hh := hN'card
    rw [hNcard] at hh
    omega
  have hfact : (Nat.card N').factorization 2 = 12 := by
    rw [hN'card', show 256 * 3600 = 2 ^ 12 * 225 by norm_num]
    exact l210A_factorization_two_pow_mul_odd 12 225 (by norm_num)
  have hcard : Nat.card K' * Nat.card D'' = 2 ^ (Nat.card N').factorization 2 := by
    rw [hK'card, hD''card, hfact]
    norm_num
  obtain ⟨C', hC'K', hC'sup⟩ :=
    exists_complement_of_two_sylow_complement (K := K') (D := D'') hK'pg hD''pg hK'D'' hcard
  let C : Subgroup N := C'.map N'.subtype
  refine ⟨C, ?_, ?_⟩
  · refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨hxC, hxK⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_map] at hxC
    obtain ⟨c', hc'C, hc'eq⟩ := hxC
    have hc'K' : c' ∈ K' := by
      change (c' : N) ∈ K
      rw [← hkerK, MonoidHom.mem_ker]
      change ψ (N'.subtype c') = 1
      rw [hc'eq]
      exact MonoidHom.mem_ker.mp hxK
    have hc'mem : c' ∈ K' ⊓ C' := ⟨hc'K', hc'C⟩
    rw [hC'K', Subgroup.mem_bot] at hc'mem
    rw [← hc'eq, hc'mem]
    simp
  · have hbase_top : (⊤ : Subgroup N').map (ψ.comp N'.subtype) = base := by
      rw [Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype, hmapN']
    have hK'bot : K'.map (ψ.comp N'.subtype) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      intro x hx
      change (x : N) ∈ K at hx
      rw [← hkerK, MonoidHom.mem_ker] at hx
      show ψ (x : N) = 1
      exact hx
    have htop : C'.map (ψ.comp N'.subtype) = base := by
      have h1 : (K' ⊔ C').map (ψ.comp N'.subtype) = base := by rw [hC'sup, hbase_top]
      rwa [Subgroup.map_sup, hK'bot, bot_sup_eq] at h1
    change (C'.map N'.subtype).map ψ = base
    rw [Subgroup.map_map]
    exact htop

end CFSG.EvenSporadicStandard.HNRecog.Harada
