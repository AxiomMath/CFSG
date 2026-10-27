module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.A5WrTwoInvolutions
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.BaseEmb

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

private theorem coord_cases (q : Multiplicative (ZMod 2)) :
    q = 1 ∨ q = Multiplicative.ofAdd (1 : ZMod 2) := by
  rcases (show ∀ e : ZMod 2, e = 0 ∨ e = 1 by decide) (Multiplicative.toAdd q) with h | h
  · left
    rw [← ofAdd_toAdd q, h]
    rfl
  · right
    rw [← ofAdd_toAdd q, h]

private theorem sigmaC2_mul_self :
    (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd (1 : ZMod 2) = 1 := by
  decide

private theorem natCard_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem natCard_base : Nat.card (commutator A5WrTwo) = 3600 := by
  rw [← A5WrTwo.range_baseEmb, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (K := ⊤) A5WrTwo.baseEmb_injective,
    Subgroup.card_top, Nat.card_prod, natCard_alt5]

private abbrev sW : A5WrTwo :=
  ⟨(1 : Multiplicative (ZMod 2) → alternatingGroup (Fin 5)),
    Multiplicative.ofAdd (1 : ZMod 2)⟩

private theorem sW_sq : sW ^ 2 = 1 := by
  apply RegularWreathProduct.ext
  · funext x
    simp [sW, pow_two, RegularWreathProduct.mul_def, sigmaC2_mul_self]
  · simp [sW, pow_two, RegularWreathProduct.mul_def, sigmaC2_mul_self]

private theorem sW_not_mem_base : sW ∉ commutator A5WrTwo := by
  rw [A5WrTwo.commutator_eq_ker, MonoidHom.mem_ker]
  decide

private theorem natCard_subgroupOf_of_le {G : Type*} [Group G] {H K : Subgroup G}
    (h : H ≤ K) : Nat.card (H.subgroupOf K) = Nat.card H := by
  rw [← Subgroup.card_subtype K (H.subgroupOf K), Subgroup.map_subgroupOf_eq_of_le h]

private theorem card_dvd_card_of_le {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card H ∣ Nat.card K := by
  rw [← natCard_subgroupOf_of_le h]
  exact Subgroup.card_subgroup_dvd_card (H.subgroupOf K)

private theorem isPGroup_two_of_sq_eq_one {E : Subgroup A5WrTwo}
    (h : ∀ x ∈ E, x ^ 2 = 1) : IsPGroup 2 E := by
  rw [isPGroup_iff_orderOf_dvd_pow]
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one, orderOf_dvd_iff_pow_eq_one]
  exact Subtype.ext (by simpa using h (g : A5WrTwo) g.2)

private theorem le_four_of_two_pow_dvd_3600 {n : ℕ} (h : 2 ^ n ∣ 3600) : n ≤ 4 := by
  by_contra hn
  have hn5 : 5 ≤ n := by omega
  have h32 : (32 : ℕ) ∣ 2 ^ n := by
    have : 2 ^ n = 2 ^ 5 * 2 ^ (n - 5) := by rw [← pow_add]; congr 1; omega
    rw [this]; exact dvd_mul_right _ _
  exact (by norm_num : ¬ (32 : ℕ) ∣ 3600) (h32.trans h)

private theorem le_two_of_two_pow_dvd_sixty {m : ℕ} (h : 2 ^ m ∣ 60) : m ≤ 2 := by
  by_contra hm
  have hm3 : 3 ≤ m := by omega
  have h8 : (8 : ℕ) ∣ 2 ^ m := by
    have : 2 ^ m = 2 ^ 3 * 2 ^ (m - 3) := by rw [← pow_add]; congr 1; omega
    rw [this]; exact dvd_mul_right _ _
  exact (by norm_num : ¬ (8 : ℕ) ∣ 60) (h8.trans h)

private def diagHom : alternatingGroup (Fin 5) →*
    alternatingGroup (Fin 5) × alternatingGroup (Fin 5) :=
  (MonoidHom.id _).prod (MonoidHom.id _)

private def diagSub : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :=
  diagHom.range

private theorem diagHom_injective : Function.Injective diagHom := by
  intro a b h
  simpa [diagHom] using congrArg Prod.fst h

private theorem natCard_diagSub : Nat.card diagSub = 60 := by
  rw [diagSub, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (K := ⊤) diagHom_injective,
    Subgroup.card_top, natCard_alt5]

private theorem centralizer_sW_inf_base :
    centralizer ({sW} : Set A5WrTwo) ⊓ commutator A5WrTwo =
      diagSub.map A5WrTwo.baseEmb := by
  ext g
  constructor
  · intro hg
    obtain ⟨hgcent, hgbase⟩ := Subgroup.mem_inf.mp hg
    rw [← A5WrTwo.range_baseEmb] at hgbase
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hgbase
    cases p with
    | mk x y =>
      have hsg : sW * g = g * sW :=
        (Subgroup.mem_centralizer_iff.mp hgcent) sW (by simp)
      have hconj : sW * g * sW⁻¹ = g := by rw [hsg]; group
      have hxy : A5WrTwo.baseEmb (y, x) = A5WrTwo.baseEmb (x, y) := by
        rw [← A5WrTwo.swap_mul_baseEmb_mul_inv x y, hp, hconj]
      have hyx : y = x := congrArg Prod.fst (A5WrTwo.baseEmb_injective hxy)
      refine Subgroup.mem_map.mpr ⟨(x, x), ?_, ?_⟩
      · rw [diagSub]
        exact MonoidHom.mem_range.mpr ⟨x, by simp [diagHom]⟩
      · rw [← hp, hyx]
  · intro hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨p, hpdiag, hpg⟩ := hg
    rw [diagSub, MonoidHom.mem_range] at hpdiag
    obtain ⟨x, hx⟩ := hpdiag
    have hx' : p = (x, x) := by rw [← hx]; simp [diagHom]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      rw [← hpg, hx']
      have hs := A5WrTwo.swap_mul_baseEmb_mul_inv x x
      calc sW * A5WrTwo.baseEmb (x, x)
          = (sW * A5WrTwo.baseEmb (x, x) * sW⁻¹) * sW := by group
        _ = A5WrTwo.baseEmb (x, x) * sW := by rw [hs]
    · rw [← A5WrTwo.range_baseEmb]
      exact MonoidHom.mem_range.mpr ⟨(x, x), by rw [← hpg, hx']⟩

private theorem natCard_centralizer_sW :
    Nat.card ↥(centralizer ({sW} : Set A5WrTwo) ⊓ commutator A5WrTwo) = 60 := by
  rw [centralizer_sW_inf_base]
  rw [Subgroup.card_map_of_injective (K := diagSub) A5WrTwo.baseEmb_injective,
    natCard_diagSub]

private theorem map_conj_centralizer_sW {b u : A5WrTwo} (hb : b * sW * b⁻¹ = u) :
    (centralizer ({sW} : Set A5WrTwo)).map (MulAut.conj b).toMonoidHom =
      centralizer ({u} : Set A5WrTwo) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    have h := congrArg (MulAut.conj b) hy
    simp only [map_mul, MulAut.conj_apply, hb] at h
    exact h
  · intro hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    refine ⟨(MulAut.conj b).symm x, ?_, (MulAut.conj b).apply_symm_apply x⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg (MulAut.conj b).symm hx
    simp only [map_mul] at h
    have hsu : (MulAut.conj b).symm u = sW := by
      rw [MulAut.conj_symm_apply, ← hb]; group
    rwa [hsu] at h

private theorem card_le_eight_of_not_le_base {D : Subgroup A5WrTwo}
    (hD : IsElemAbelian 2 D) (hDnot : ¬ D ≤ commutator A5WrTwo) :
    Nat.card D ≤ 8 := by
  obtain ⟨u, huD, hubase⟩ : ∃ u ∈ D, u ∉ commutator A5WrTwo := by
    by_contra h
    push_neg at h
    exact hDnot fun x hx => h x hx
  have hu2 : u ^ 2 = 1 := hD.2 u huD
  obtain ⟨b, _hbbase, hbconj⟩ :=
    A5WrTwo.exists_conj_of_outer_involutions sW_not_mem_base hubase sW_sq hu2
  let f : D →* Multiplicative (ZMod 2) :=
    (RegularWreathProduct.rightHom : A5WrTwo →* Multiplicative (ZMod 2)).comp D.subtype
  have hfu : f ⟨u, huD⟩ ≠ 1 := by
    intro h
    apply hubase
    rw [A5WrTwo.commutator_eq_ker, MonoidHom.mem_ker]
    simpa [f] using h
  have hrange : f.range = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro x
    rcases coord_cases x with rfl | rfl
    · exact f.range.one_mem
    · have hfu' : f ⟨u, huD⟩ = Multiplicative.ofAdd 1 := by
        rcases coord_cases (f ⟨u, huD⟩) with h | h
        · exact absurd h hfu
        · exact h
      rw [← hfu']
      exact MonoidHom.mem_range.mpr ⟨⟨u, huD⟩, rfl⟩
  have hindex : f.ker.index = 2 := by
    rw [Subgroup.index_ker, hrange, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hker_eq : f.ker = (D ⊓ commutator A5WrTwo).subgroupOf D := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MonoidHom.mem_ker]
    constructor
    · intro hx
      exact ⟨x.2, by
        rw [A5WrTwo.commutator_eq_ker, MonoidHom.mem_ker]
        simpa [f] using hx⟩
    · rintro ⟨-, hx⟩
      rw [A5WrTwo.commutator_eq_ker, MonoidHom.mem_ker] at hx
      simpa [f] using hx
  have hcardD : Nat.card D = 2 * Nat.card ↥(D ⊓ commutator A5WrTwo) := by
    have hcard_ker : Nat.card f.ker = Nat.card ↥(D ⊓ commutator A5WrTwo) := by
      rw [hker_eq, natCard_subgroupOf_of_le (inf_le_left : D ⊓ commutator A5WrTwo ≤ D)]
    have h := Subgroup.card_mul_index (H := f.ker)
    rw [hindex, hcard_ker, mul_comm] at h
    exact h.symm
  have hDbase_le_Zu : D ⊓ commutator A5WrTwo ≤ centralizer ({u} : Set A5WrTwo) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxD : x ∈ D := (Subgroup.mem_inf.mp hx).1
    haveI : IsMulCommutative D := hD.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hxD⟩ : D) (⟨u, huD⟩ : D))
  have hle_Zu : D ⊓ commutator A5WrTwo ≤
      centralizer ({u} : Set A5WrTwo) ⊓ commutator A5WrTwo := by
    intro x hx
    exact ⟨hDbase_le_Zu hx, (Subgroup.mem_inf.mp hx).2⟩
  have hcard_conj : Nat.card ↥(centralizer ({u} : Set A5WrTwo) ⊓ commutator A5WrTwo) =
      Nat.card ↥(centralizer ({sW} : Set A5WrTwo) ⊓ commutator A5WrTwo) := by
    haveI : (commutator A5WrTwo).Normal := by
      rw [A5WrTwo.commutator_eq_ker]
      infer_instance
    have hB : (commutator A5WrTwo).map (MulAut.conj b).toMonoidHom =
        commutator A5WrTwo := Subgroup.Normal.map_conj_eq (commutator A5WrTwo) b
    have hmap : (centralizer ({sW} : Set A5WrTwo) ⊓ commutator A5WrTwo).map
          (MulAut.conj b).toMonoidHom =
        centralizer ({u} : Set A5WrTwo) ⊓ commutator A5WrTwo := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj b).injective,
        map_conj_centralizer_sW hbconj, hB]
    rw [← hmap]
    exact Subgroup.card_map_of_injective (MulAut.conj b).injective
  have hdvd : Nat.card ↥(D ⊓ commutator A5WrTwo) ∣
      Nat.card ↥(centralizer ({u} : Set A5WrTwo) ⊓ commutator A5WrTwo) :=
    card_dvd_card_of_le hle_Zu
  rw [hcard_conj, natCard_centralizer_sW] at hdvd
  have h2g : IsPGroup 2 ↥(D ⊓ commutator A5WrTwo) :=
    isPGroup_two_of_sq_eq_one fun x hx => hD.2 x (Subgroup.mem_inf.mp hx).1
  obtain ⟨m, hm⟩ := h2g.exists_card_eq
  have hpow : 2 ^ m ∣ 60 := by rw [← hm]; exact hdvd
  have hmle : m ≤ 2 := le_two_of_two_pow_dvd_sixty hpow
  have hbase_le : Nat.card ↥(D ⊓ commutator A5WrTwo) ≤ 4 := by
    rw [hm]
    calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hmle
      _ = 4 := by norm_num
  calc Nat.card D = 2 * Nat.card ↥(D ⊓ commutator A5WrTwo) := hcardD
    _ ≤ 2 * 4 := Nat.mul_le_mul_left 2 hbase_le
    _ = 8 := by norm_num

theorem L210_card_le_sixteen_of_isElemAbelian {D : Subgroup A5WrTwo} (hD : IsElemAbelian 2 D) :
    Nat.card D ≤ 16 := by
  by_cases hbase : D ≤ commutator A5WrTwo
  · have h2g : IsPGroup 2 D := isPGroup_two_of_sq_eq_one hD.2
    obtain ⟨n, hn⟩ := h2g.exists_card_eq
    have hdvd : Nat.card D ∣ 3600 := by
      rw [← natCard_base]
      exact card_dvd_card_of_le hbase
    have hnle : n ≤ 4 := by
      apply le_four_of_two_pow_dvd_3600
      rwa [← hn]
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hnle
      _ = 16 := by norm_num
  · have hle8 : Nat.card D ≤ 8 := card_le_eight_of_not_le_base hD hbase
    omega

theorem L210_le_base_of_eight_lt_card {D : Subgroup A5WrTwo} (hD : IsElemAbelian 2 D)
    (h : 8 < Nat.card D) : D ≤ commutator A5WrTwo := by
  by_contra hnot
  exact absurd (card_le_eight_of_not_le_base hD hnot) (by omega)

end CFSG.EvenSporadicStandard.HNRecog.Harada
