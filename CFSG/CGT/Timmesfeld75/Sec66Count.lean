module

public import CFSG.CGT.Timmesfeld75.Sec66Conj
public import CFSG.CGT.Timmesfeld75.Sec4OneQuotient
public import CFSG.CGT.Timmesfeld75.Sec3Root
public import CFSG.CGT.Timmesfeld75.Sec3Iso
public import CFSG.CGT.Timmesfeld75.Sec3L2
public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Step511Card
public import CFSG.CGT.Timmesfeld75.Step57Reduction

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem Sec3.exists_fixed_conj_swap [Finite G] (hS : Sec3 T T₁) (hI : Sec3Iso T T₁) {y : G}
    (hyy : y * y = 1) (hy : conjSubgroup y T = T₁) :
    ∃ g ∈ T ⊔ T₁, conjSubgroup y (conjSubgroup g T) = conjSubgroup g T := by
  have hyT₁ : conjSubgroup y T₁ = T := by
    rw [← hy, conjSubgroup_conjSubgroup, hyy, conjSubgroup_one]
  have hyX : y ∈ Subgroup.normalizer ((T ⊔ T₁ : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_conjSubgroup_eq, conjSubgroup_sup_eq_sup, hy, hyT₁, sup_comm]
  have hyM : y ∈ Subgroup.normalizer (cfgM T T₁ : Set G) := by
    rw [mem_normalizer_iff_conjSubgroup_eq, ← cfgM_conj, hy, hyT₁, cfgM_symm]
  obtain ⟨hN, f, hf, hiso⟩ := hI
  have := hN
  have hpair := hS.isL2Pair_quotient hf hiso
  obtain ⟨g, hg, hfix⟩ := exists_fixed_conj_of_involution (U := T) le_sup_left hpair hyy hyX hyM
  refine ⟨g, hg, ?_⟩
  have hwc : IsWC (conjSubgroup g T) := hS.cfg.wc.conj g
  have hM2 : IsPGroup 2 (cfgM T T₁) := isPGroup_two_of_isElemAbelian hS.cfg.isElemAbelian_cfgM
  have hS2 : IsPGroup 2 (conjSubgroup g T) :=
    isPGroup_two_of_isElemAbelian (isElemAbelian_conjSubgroup hS.cfg.wc.1 g)
  have hXN : T ⊔ T₁ ≤ Subgroup.normalizer (cfgM T T₁ : Set G) := hS.cfg.le_normalizer_cfgM
  have hSX : conjSubgroup g T ≤ T ⊔ T₁ := conjSubgroup_le_of_le_of_mem le_sup_left hg
  have hP : IsPGroup 2 ↥(conjSubgroup g T ⊔ cfgM T T₁) :=
    hS2.to_sup_of_normal_right' hM2 (fun u hu => hXN (hSX hu))
  have hle : conjSubgroup y (conjSubgroup g T) ≤ conjSubgroup g T ⊔ cfgM T T₁ := by
    intro z hz
    have hz' : y⁻¹ * z * y ∈ conjSubgroup g T := mem_conjSubgroup.1 hz
    obtain ⟨u', hu', n', hn', he⟩ := hfix (y⁻¹ * z * y) hz'
    have e : z = u' * n' := by
      have := he
      rw [show y * (y⁻¹ * z * y) * y⁻¹ = z by group] at this
      exact this
    rw [e]
    exact Subgroup.mul_mem_sup hu' hn'
  exact eq_of_conj_le_pGroup hwc hP le_sup_left hle

section Count

variable [Finite G]

omit [Finite G] in
theorem conj_mem_normIn_swap {y l : G} (hyy : y * y = 1) (hl : l ∈ normIn T (conjSubgroup y T)) :
    y * l * y⁻¹ ∈ normIn (conjSubgroup y T) T := by
  have hT : conjSubgroup y (conjSubgroup y T) = T := by
    rw [conjSubgroup_conjSubgroup, hyy, conjSubgroup_one]
  have e := normIn_conj y T (conjSubgroup y T)
  rw [hT] at e
  have := conj_mem_conjSubgroup y hl
  rwa [← e] at this

omit [Finite G] in
theorem conj_mem_normIn_swap' {y z : G} (hyy : y * y = 1)
    (hz : z ∈ normIn (conjSubgroup y T) T) : y * z * y⁻¹ ∈ normIn T (conjSubgroup y T) := by
  have hT : conjSubgroup y (conjSubgroup y T) = T := by
    rw [conjSubgroup_conjSubgroup, hyy, conjSubgroup_one]
  have e := normIn_conj y (conjSubgroup y T) T
  rw [hT] at e
  have := conj_mem_conjSubgroup y hz
  rwa [← e] at this

theorem Sec6Ctx.card_normIn_le_sq_aux (h62 : Sec62) (h63 : Sec63) (hc : Sec6Ctx T T₁ n m)
    {y g : G} (hyD : y ∈ classD T) (hyy : y * y = 1)
    (hS3 : Sec3 T (conjSubgroup y T)) (hg : g ∈ T ⊔ conjSubgroup y T)
    (hfix : conjSubgroup y (conjSubgroup g T) = conjSubgroup g T)
    (hyS : y ∉ conjSubgroup g T) :
    Nat.card ↥(normIn T (conjSubgroup y T)) ≤
        Nat.card ↥(conjSubgroup g T ⊓ cfgM T (conjSubgroup y T) ⊓
          Subgroup.centralizer ({y} : Set G)) ^ 2 ∧
      conjSubgroup g T ⊓ cfgM T (conjSubgroup y T) ⊓ Subgroup.centralizer ({y} : Set G) ≤
        commSub y (conjSubgroup g T) := by
  set T' := conjSubgroup y T with hT'
  set S := conjSubgroup g T with hSdef
  set M := cfgM T T' with hMdef
  have hy2 : y ^ 2 = 1 := by rw [pow_two]; exact hyy
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hT'y : conjSubgroup y T' = T := by
    rw [hT', conjSubgroup_conjSubgroup, hyy, conjSubgroup_one]
  have hyM : conjSubgroup y M = M := by
    rw [hMdef, ← cfgM_conj, hT'y, ← hT', cfgM_symm]
  have hgM : conjSubgroup g M = M :=
    mem_normalizer_iff_conjSubgroup_eq.1 (hS3.cfg.le_normalizer_cfgM hg)
  have hM2 : IsElemAbelian 2 M := hS3.cfg.isElemAbelian_cfgM
  have hSab : IsElemAbelian 2 S := isElemAbelian_conjSubgroup hS3.cfg.wc.1 g
  set A := S ⊓ M with hAdef
  have hA : A = conjSubgroup g (normIn T T') := by
    rw [← hS3.cfg.inf_cfgM, conjSubgroup_inf_eq_inf, hgM]
  have hAcard : Nat.card ↥A = Nat.card ↥(normIn T T') := by
    rw [hA, card_conjSubgroup]
  have hyA : conjSubgroup y A = A := by
    rw [hAdef, conjSubgroup_inf_eq_inf, hfix, hyM]
  have hAab : IsElemAbelian 2 A := isElemAbelian_of_le hSab inf_le_left
  have hyAN : y ∈ Subgroup.normalizer (A : Set G) := mem_normalizer_iff_conjSubgroup_eq.2 hyA
  have hySN : y ∈ Subgroup.normalizer (S : Set G) := mem_normalizer_iff_conjSubgroup_eq.2 hfix
  have h23 := card_commSub_mul_card_centralizer hAab hy2 hyAN
  have hle := commSub_le hAab hy2 hyAN
  have hsq : Nat.card ↥A ≤ Nat.card ↥(A ⊓ Subgroup.centralizer ({y} : Set G)) ^ 2 := by
    rw [← h23, pow_two]
    exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hle)
  have hCA : A ⊓ Subgroup.centralizer ({y} : Set G) ≤ commSub y S := by
    rintro c ⟨hcA, hcC⟩
    have hcS : c ∈ S := hcA.1
    have hcM : c ∈ M := hcA.2
    have hcy : c * y = y * c := Subgroup.mem_centralizer_singleton_iff.1 hcC
    obtain ⟨l, hl, z, hz, rfl⟩ := hS3.cfg.mem_cfgM_iff.1 hcM
    have hlT : l ∈ T := normIn_le _ _ hl
    have hzT' : z ∈ T' := normIn_le _ _ hz
    set a := y * z * y⁻¹ with ha
    set b := y * l * y⁻¹ with hb
    have haL : a ∈ normIn T T' := conj_mem_normIn_swap' hyy hz
    have hbL : b ∈ normIn T' T := conj_mem_normIn_swap hyy hl
    have haM : a ∈ M := Cfg.normIn_le_cfgM_left T T' haL
    have hbM : b ∈ M := Cfg.normIn_le_cfgM_right T T' hbL
    have hlM : l ∈ M := Cfg.normIn_le_cfgM_left T T' hl
    have hzM : z ∈ M := Cfg.normIn_le_cfgM_right T T' hz
    have hyc : y * (l * z) * y⁻¹ = l * z := by
      have : y * (l * z) = (l * z) * y := hcy.symm
      rw [this]; group
    have e1 : y * (l * z) * y⁻¹ = b * a := by
      rw [hb, ha]; group
    have hba : b * a = a * b := elemAbelian_mul_comm hM2 hbM haM
    have e2 : l * z = a * b := by rw [← hyc, e1, hba]
    have hmem : a⁻¹ * l ∈ T ⊓ T' := by
      refine ⟨T.mul_mem (T.inv_mem (normIn_le _ _ haL)) hlT, ?_⟩
      have e3 : a⁻¹ * l = b * z⁻¹ := by
        have h4 : a⁻¹ * (l * z) = b := by rw [e2]; group
        calc a⁻¹ * l = (a⁻¹ * (l * z)) * z⁻¹ := by group
          _ = b * z⁻¹ := by rw [h4]
      rw [e3]
      exact T'.mul_mem (normIn_le _ _ hbL) (T'.inv_mem hzT')
    rw [hS3.cfg.inf, Subgroup.mem_bot] at hmem
    have hal : l = a := by
      have := hmem
      rw [inv_mul_eq_one] at this
      exact this.symm
    have hbz : b = z := by
      have h4 : a⁻¹ * (l * z) = b := by rw [e2]; group
      rw [← hal] at h4
      have h5 : z = b := by
        have : l⁻¹ * (l * z) = b := h4
        simpa using this
      exact h5.symm
    have hli : l⁻¹ = l := elemAbelian_inv hS3.cfg.wc.1 hlT
    have hycD : y * (l * z) ∈ classD T := by
      have e4 : y * (l * z) = l * y * l := by
        have h1 : y * (l * z) = (l * z) * y := hcy.symm
        rw [h1, ← hbz, hb]
        group
      rw [e4]
      have := classD_conj hyD l
      rwa [hli] at this
    obtain ⟨s, hs, hsy⟩ := hc.eq_conj_of_mem_coset_conj h62 h63 hyD hySN hyS hcS hycD
    refine (mem_commSub_iff hSab hy2 hySN).2 ⟨s, hs, ?_⟩
    have hsi : s⁻¹ = s := elemAbelian_inv hSab hs
    have e5 : l * z = y⁻¹ * (y * (l * z)) := by group
    rw [commutatorElement_def, e5, hsy, hyi, hsi]
    group
  exact ⟨by rw [← hAcard]; exact hsq, hCA⟩

end Count

end CFSG.CGT.Timmesfeld75
