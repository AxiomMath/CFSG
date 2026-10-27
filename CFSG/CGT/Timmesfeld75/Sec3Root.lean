module

public import CFSG.CGT.Timmesfeld75.Sec3Odd
public import CFSG.LieType.BorelTits.Basic
public import CFSG.Timmesfeld.Defs

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section ClassDIn

variable {G : Type*} [Group G]

@[expose] def classDIn (X T : Subgroup G) : Set G :=
  {t | t ≠ 1 ∧ ∃ x ∈ X, t ∈ conjSubgroup x T}

theorem classDIn_conj_subset {X U T : Subgroup G} {h : G} (hXU : X ≤ U) (hh : h ∈ U) :
    classDIn X (conjSubgroup h T) ⊆ classDIn U T := by
  rintro t ⟨ht1, x, hx, htx⟩
  refine ⟨ht1, x * h, U.mul_mem (hXU hx) hh, ?_⟩
  rwa [conjSubgroup_conjSubgroup] at htx

theorem orderOf_eq_two_of_mem_classDIn {X T : Subgroup G} (hT : IsElemAbelian 2 T) {d : G}
    (hd : d ∈ classDIn X T) : orderOf d = 2 := by
  obtain ⟨hd1, x, -, hdx⟩ := hd
  exact orderOf_eq_prime ((isElemAbelian_conjSubgroup hT x).2 d hdx) hd1

theorem orderOf_cases_of_pow_four {g : G} (h : g ^ 4 = 1) :
    orderOf g = 2 ∨ orderOf g = 4 ∨ Odd (orderOf g) := by
  rcases (Nat.dvd_prime_pow Nat.prime_two).1
    (show orderOf g ∣ 2 ^ 2 by simpa using orderOf_dvd_of_pow_eq_one h) with ⟨i, hi, hgi⟩
  interval_cases i
  · exact Or.inr (Or.inr (by rw [hgi]; exact odd_one))
  · exact Or.inl (by simpa using hgi)
  · exact Or.inr (Or.inl (by simpa using hgi))

theorem cases_of_sq_mem_conjSubgroup {X T : Subgroup G} (hT : IsElemAbelian 2 T) {y g : G}
    (hy : y ∈ X) (hg : g ^ 2 ∈ conjSubgroup y T) :
    (orderOf g = 2 ∨ orderOf g = 4 ∨ Odd (orderOf g)) ∧
      (orderOf g = 4 → g ^ 2 ∈ classDIn X T) := by
  refine ⟨orderOf_cases_of_pow_four ?_, fun h4 => ⟨?_, y, hy, hg⟩⟩
  · rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
    exact (isElemAbelian_conjSubgroup hT y).2 _ hg
  · exact pow_ne_one_of_lt_orderOf (by norm_num) (by omega)

end ClassDIn

section Root

variable {G : Type*} [Group G] {T T₁ : Subgroup G}

theorem Sec3.sq_mul_mem_conjSubgroup_normIn (hS : Sec3 T T₁) {y d e : G} (hy : y ∈ T ⊔ T₁)
    (he : e ∈ conjSubgroup y T) (heM : e ∉ cfgM T T₁) (hd : d ∈ cfgM T T₁) :
    (d * e) ^ 2 ∈ conjSubgroup y (normIn T T₁) := by
  have heX : e ∈ T ⊔ T₁ := conjSubgroup_le_of_le_of_mem le_sup_left hy he
  have hM := hS.cfg.isElemAbelian_cfgM
  have hee : e * e = 1 := elemAbelian_mul_self (isElemAbelian_conjSubgroup hS.cfg.wc.1 y) he
  have hdd : d * d = 1 := elemAbelian_mul_self hM hd
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have hsq : (d * e) ^ 2 = d * (e * d * e⁻¹) := by
    rw [hei, pow_two]
    simp only [mul_assoc]
  have hsqM : (d * e) ^ 2 ∈ cfgM T T₁ := by
    rw [hsq]
    exact (cfgM T T₁).mul_mem hd (hS.cfg.conj_mem_cfgM heX hd)
  have h1 : e * (d * e) * e⁻¹ = (d * e)⁻¹ := by
    rw [show e * (d * e) * e⁻¹ = e * d by group, mul_inv_rev, hei, hdi]
  have h2 : e * (d * e) ^ 2 * e⁻¹ = (d * e) ^ 2 := by
    rw [← conj_pow, h1, inv_pow, elemAbelian_inv hM hsqM]
  have hC : (d * e) ^ 2 ∈ Subgroup.centralizer ({e} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  rw [← hS.cfgM_inf_centralizer_conj hy he heM]
  exact ⟨hsqM, hC⟩

variable [Finite G]

theorem Sec3.orderOf_mul_cases (hS : Sec3 T T₁) {d e : G} (hd : d ∈ classDIn (T ⊔ T₁) T)
    (he : e ∈ classDIn (T ⊔ T₁) T) :
    (orderOf (d * e) = 2 ∨ orderOf (d * e) = 4 ∨ Odd (orderOf (d * e))) ∧
      (orderOf (d * e) = 4 → (d * e) ^ 2 ∈ classDIn (T ⊔ T₁) T) := by
  obtain ⟨hd1, x, hx, hdx⟩ := hd
  obtain ⟨he1, y, hy, hey⟩ := he
  have hT := hS.cfg.wc.1
  have hM := hS.cfg.isElemAbelian_cfgM
  by_cases hdM : d ∈ cfgM T T₁
  · by_cases heM : e ∈ cfgM T T₁
    · have h2 : (d * e) ^ 2 = 1 := hM.2 _ ((cfgM T T₁).mul_mem hdM heM)
      exact cases_of_sq_mem_conjSubgroup hT (y := 1) (T ⊔ T₁).one_mem
        (by rw [h2]; exact (conjSubgroup 1 T).one_mem)
    · exact cases_of_sq_mem_conjSubgroup hT hy
        (conjSubgroup_mono (normIn_le T T₁) (hS.sq_mul_mem_conjSubgroup_normIn hy hey heM hdM))
  · by_cases heM : e ∈ cfgM T T₁
    · have hdd : d * d = 1 := elemAbelian_mul_self (isElemAbelian_conjSubgroup hT x) hdx
      have hee : e * e = 1 := elemAbelian_mul_self hM heM
      have hde : d * e = (e * d)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hdd, inv_eq_of_mul_eq_one_right hee]
      refine cases_of_sq_mem_conjSubgroup hT hx ?_
      rw [hde, inv_pow]
      exact (conjSubgroup x T).inv_mem
        (conjSubgroup_mono (normIn_le T T₁) (hS.sq_mul_mem_conjSubgroup_normIn hx hdx hdM heM))
    · by_cases hxy : conjSubgroup x T = conjSubgroup y T
      · have hde : d * e ∈ conjSubgroup x T := (conjSubgroup x T).mul_mem hdx (hxy ▸ hey)
        have h2 : (d * e) ^ 2 = 1 := (isElemAbelian_conjSubgroup hT x).2 _ hde
        exact cases_of_sq_mem_conjSubgroup hT hx (by rw [h2]; exact (conjSubgroup x T).one_mem)
      · have hodd := hS.odd_orderOf_mul hx hy hxy hdx hdM hey heM
        exact ⟨Or.inr (Or.inr hodd), fun h4 => absurd (h4 ▸ hodd) (by decide)⟩

theorem Sec3.isRootInvolutionSet (hS : Sec3 T T₁) :
    CFSG.Timmesfeld.IsRootInvolutionSet (classDIn (T ⊔ T₁) T) :=
  ⟨fun _ hd => orderOf_eq_two_of_mem_classDIn hS.cfg.wc.1 hd,
    fun _ hd _ he => (hS.orderOf_mul_cases hd he).1,
    fun _ hd _ he => (hS.orderOf_mul_cases hd he).2⟩

end Root

section PCore

variable {G : Type*} [Group G] [Finite G] {T U : Subgroup G}

theorem pCoreOf_le_normalizer_of_isWC (hT : IsWC T) (hTU : T ≤ U) :
    pCoreOf 2 U ≤ Subgroup.normalizer (T : Set G) := by
  intro o ho
  have hUO := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 U
  have hS : IsPGroup 2 ↥(T ⊔ pCoreOf 2 U) :=
    (isPGroup_two_of_isElemAbelian hT.1).to_sup_of_normal_right'
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 U)
      (hTU.trans hUO)
  have hle : conjSubgroup o T ≤ T ⊔ pCoreOf 2 U := by
    intro y hy
    have ht : o⁻¹ * y * o ∈ T := mem_conjSubgroup.1 hy
    have h1 : (o⁻¹ * y * o) * o⁻¹ * (o⁻¹ * y * o)⁻¹ ∈ pCoreOf 2 U :=
      ((Subgroup.mem_normalizer_iff.1 (hUO (hTU ht))) o⁻¹).1 ((pCoreOf 2 U).inv_mem ho)
    have e : y = (o * ((o⁻¹ * y * o) * o⁻¹ * (o⁻¹ * y * o)⁻¹)) * (o⁻¹ * y * o) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ((pCoreOf 2 U).mul_mem ho h1))
      (Subgroup.mem_sup_left ht)
  exact mem_normalizer_of_conjSubgroup_eq (eq_of_conj_le_pGroup hT hS le_sup_left hle)

theorem pCoreOf_le_normalizer_conjSubgroup (hT : IsWC T) (hTU : T ≤ U) {g : G} (hg : g ∈ U) :
    pCoreOf 2 U ≤ Subgroup.normalizer (conjSubgroup g T : Set G) := by
  intro o ho
  rw [mem_normalizer_conjSubgroup_iff]
  have hUO := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 U
  have h1 : g⁻¹ * o * g ∈ pCoreOf 2 U := by
    simpa using ((Subgroup.mem_normalizer_iff.1 (hUO (U.inv_mem hg))) o).1 ho
  exact pCoreOf_le_normalizer_of_isWC hT hTU h1

theorem conjSubgroup_inf_pCoreOf_ne_bot (hT : IsWC T) (hTU : T ≤ U)
    (hO : ⁅pCoreOf 2 U, T⁆ ≠ ⊥) {h : G} (hh : h ∈ U) :
    conjSubgroup h T ⊓ pCoreOf 2 U ≠ ⊥ := by
  have hUO := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 U
  have hcomm : ⁅pCoreOf 2 U, T⁆ ≤ T ⊓ pCoreOf 2 U := by
    rw [Subgroup.commutator_le]
    intro o ho t ht
    refine ⟨comm_mem_of_mem_normalizer (pCoreOf_le_normalizer_of_isWC hT hTU ho) ht, ?_⟩
    have h1 : t * o⁻¹ * t⁻¹ ∈ pCoreOf 2 U :=
      ((Subgroup.mem_normalizer_iff.1 (hUO (hTU ht))) o⁻¹).1 ((pCoreOf 2 U).inv_mem ho)
    have e : ⁅o, t⁆ = o * (t * o⁻¹ * t⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (pCoreOf 2 U).mul_mem ho h1
  have hne : T ⊓ pCoreOf 2 U ≠ ⊥ := fun hb => hO (le_bot_iff.1 (hcomm.trans hb.le))
  have hconjO : conjSubgroup h (pCoreOf 2 U) = pCoreOf 2 U :=
    mem_normalizer_iff_conjSubgroup_eq.1 (hUO hh)
  have e : conjSubgroup h T ⊓ pCoreOf 2 U = conjSubgroup h (T ⊓ pCoreOf 2 U) := by
    rw [conjSubgroup_inf, hconjO]
  rw [e]
  exact fun hb => hne (conjSubgroup_eq_bot_iff.1 hb)

theorem normIn_conjSubgroup_ne_bot_of_pCoreOf (hT : IsWC T) (hTU : T ≤ U)
    (hO : ⁅pCoreOf 2 U, T⁆ ≠ ⊥) {h g : G} (hh : h ∈ U) (hg : g ∈ U) :
    normIn (conjSubgroup h T) (conjSubgroup g T) ≠ ⊥ := by
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (conjSubgroup_inf_pCoreOf_ne_bot hT hTU hO hh)
  refine Subgroup.ne_bot_iff_exists_ne_one.2
    ⟨⟨z, mem_normIn.2 ⟨hz.1, pCoreOf_le_normalizer_conjSubgroup hT hTU hg hz.2⟩⟩, fun h' => ?_⟩
  have h'' : z = 1 := by simpa using Subtype.ext_iff.1 h'
  exact hz1 (Subtype.ext h'')

end PCore

end CFSG.CGT.Timmesfeld75
