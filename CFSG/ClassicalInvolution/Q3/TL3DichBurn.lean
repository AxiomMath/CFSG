module

public import CFSG.ClassicalInvolution.Asc77.AscSixBasic
public import CFSG.LinearAlgebra.LinearGroups.CyclicSylowIndexTwo

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.ClassicalInvolution.Asc77

variable {X : Type} [Group X]

theorem eq_of_sq_eq_one_of_isCyclic [Finite X] [IsCyclic X] {a b : X} (ha : a * a = 1)
    (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  have : Fintype X := Fintype.ofFinite X
  by_contra hab
  have hle := IsCyclic.card_pow_eq_one_le (α := X) (n := 2) (by norm_num)
  have hsub : ({1, a, b} : Finset X) ⊆ Finset.univ.filter (fun x : X => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pow_two]
    rcases hx with rfl | rfl | rfl
    · exact one_mul 1
    · exact ha
    · exact hb
  have hcard : ({1, a, b} : Finset X).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm ha1, Ne.symm hb1⟩
  have := Finset.card_le_card hsub
  omega

theorem not_isCyclic_of_isSylow2In_centralizer [Finite X] {I V : Subgroup X}
    (hsimp : IsSimpleGroup ↥I) (hnab : ∃ a b : ↥I, a * b ≠ b * a) {i : X} (hiI : i ∈ I)
    (hi2 : i * i = 1) (hi1 : i ≠ 1) (hV : IsSylow2In V (I ⊓ Subgroup.centralizer ({i} : Set X))) :
    ¬ IsCyclic ↥V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hcyc
  have hVle : V ≤ I ⊓ Subgroup.centralizer ({i} : Set X) := hV.1
  have hV2 : IsPGroup 2 ↥V := hV.2.1
  have hzi : IsPGroup 2 ↥(Subgroup.zpowers i) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hi2) hi1]; norm_num)
  have hiV : i ∈ V := by
    have hzN : Subgroup.zpowers i ≤ Subgroup.normalizer (V : Set X) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv => ?_)
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hVle hv).2)
    have hW2 : IsPGroup 2 ↥(Subgroup.zpowers i ⊔ V) := hzi.to_sup_of_normal_right' hV2 hzN
    have hWle : Subgroup.zpowers i ⊔ V ≤ I ⊓ Subgroup.centralizer ({i} : Set X) := by
      refine sup_le ?_ hVle
      rw [Subgroup.zpowers_le]
      exact ⟨hiI, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have heq := hV.eq_of_le hW2 hWle le_sup_right
    rw [← heq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers i)
  obtain ⟨P, hP, hVP⟩ := IsSylow2In.exists_ge hV2 (hVle.trans inf_le_left)
  have hP2 : IsPGroup 2 ↥P := hP.2.1
  have hCP : P ⊓ Subgroup.centralizer ({i} : Set X) = V := by
    refine hV.eq_of_le (hP2.to_le inf_le_left) ?_ (le_inf hVP (hVle.trans inf_le_right))
    exact inf_le_inf_right _ hP.1
  have hVeq : V = P := by
    by_contra hne
    have hlt : V.subgroupOf P < ⊤ := by
      refine lt_of_le_of_ne le_top fun h => hne ?_
      apply le_antisymm hVP
      intro x hx
      have : (⟨x, hx⟩ : ↥P) ∈ V.subgroupOf P := by rw [h]; trivial
      exact this
    have hnil : Group.IsNilpotent ↥P := hP2.isNilpotent
    have hN := Group.normalizerCondition_of_isNilpotent (G := ↥P) _ hlt
    obtain ⟨g, hgN, hgV⟩ := IsConcreteLE.exists_of_lt hN
    have hgN' : (g : X) ∈ Subgroup.normalizer (V : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro v
      have hg := (Subgroup.mem_normalizer_iff.mp hgN)
      constructor
      · intro hv
        have hvP : v ∈ P := hVP hv
        have := (hg ⟨v, hvP⟩).mp (show (⟨v, hvP⟩ : ↥P) ∈ V.subgroupOf P from hv)
        exact this
      · intro hv
        have hvP : (g : X) * v * (g : X)⁻¹ ∈ P := hVP hv
        have hvP' : v ∈ P := by
          have e : v = (g : X)⁻¹ * ((g : X) * v * (g : X)⁻¹) * (g : X) := by group
          rw [e]
          exact P.mul_mem (P.mul_mem (P.inv_mem g.2) hvP) g.2
        have := (hg ⟨v, hvP'⟩).mpr (show g * ⟨v, hvP'⟩ * g⁻¹ ∈ V.subgroupOf P from hv)
        exact this
    have hgi : (g : X) * i * (g : X)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp hgN' i).mp hiV
    have hgi2 : ((g : X) * i * (g : X)⁻¹) * ((g : X) * i * (g : X)⁻¹) = 1 := by
      calc ((g : X) * i * (g : X)⁻¹) * ((g : X) * i * (g : X)⁻¹)
          = (g : X) * (i * i) * (g : X)⁻¹ := by group
        _ = 1 := by rw [hi2]; group
    have hgi1 : (g : X) * i * (g : X)⁻¹ ≠ 1 := by
      intro h
      apply hi1
      calc i = (g : X)⁻¹ * ((g : X) * i * (g : X)⁻¹) * (g : X) := by group
        _ = 1 := by rw [h]; group
    have heqi : (g : X) * i * (g : X)⁻¹ = i := by
      have := eq_of_sq_eq_one_of_isCyclic (X := ↥V) (a := ⟨_, hgi⟩) (b := ⟨i, hiV⟩)
        (Subtype.ext hgi2) (Subtype.ext hi2)
        (fun h => hgi1 (congrArg Subtype.val h)) (fun h => hi1 (congrArg Subtype.val h))
      exact congrArg Subtype.val this
    have hgC : (g : X) ∈ P ⊓ Subgroup.centralizer ({i} : Set X) := by
      refine ⟨g.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc (g : X) * i = (g : X) * i * (g : X)⁻¹ * (g : X) := by group
        _ = i * (g : X) := by rw [heqi]
    rw [hCP] at hgC
    exact hgV hgC
  have hPcyc : IsCyclic ↥P := hVeq ▸ hcyc
  let Q : Sylow 2 ↥I :=
    { toSubgroup := P.subgroupOf I
      isPGroup' := hP2.comap_subtype
      is_maximal' := by
        intro Q' hQ' hle
        have hPQ : P ≤ Q'.map I.subtype := by
          rw [← Subgroup.map_subgroupOf_eq_of_le hP.1]
          exact Subgroup.map_mono hle
        have := hP.2.2 (Q'.map I.subtype) (Subgroup.map_subtype_le _) (hQ'.map _) hPQ
        rw [← Subgroup.comap_map_eq_self_of_injective I.subtype_injective Q', this]
        rfl }
  have hQcyc : IsCyclic ↥(Q : Subgroup ↥I) := by
    have e : ↥(P.subgroupOf I) ≃* ↥P := Subgroup.subgroupOfEquivOfLe hP.1
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have : Fintype ↥I := Fintype.ofFinite _
  have hev : Even (Fintype.card ↥I) := by
    rw [← Nat.card_eq_fintype_card]
    have h2 : 2 ∣ Nat.card ↥I := by
      have hord : orderOf (⟨i, hiI⟩ : ↥I) = 2 := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_eq_prime (by rw [pow_two]; exact hi2) hi1
      rw [← hord]
      exact orderOf_dvd_natCard _
    exact even_iff_two_dvd.mpr h2
  obtain ⟨-, -, hKn, hKi⟩ := CFSG.LinearGroups.cyclic_sylow_index_two hev Q hQcyc
  set K := (Equiv.Perm.sign.comp (MulAction.toPermHom ↥I ↥I)).ker
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimp K hKn with hbot | htop
  ·
    obtain ⟨a, b, hab⟩ := hnab
    have hcard : Nat.card ↥I = 2 := by
      rw [hbot] at hKi
      rwa [Subgroup.index_bot] at hKi
    have : IsCyclic ↥I := isCyclic_of_prime_card hcard
    exact hab (mul_comm a b)
  · rw [htop, Subgroup.index_top] at hKi
    omega

end CFSG.ClassicalInvolution.Q3
