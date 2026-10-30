module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.M12Model
public import CFSG.Assembly.Defs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup CFSG.Open

variable {G : Type*} [Group G] {x₁ x₂ lam tau : G}

private abbrev m12decEq : DecidableEq M12Mod := M12Mod.equivProd.decidableEq

attribute [local instance 2000] m12decEq

private instance : Finite M12Mod :=
  Finite.of_equiv (Fin 4 × Fin 4 × Fin 2 × Fin 2) M12Mod.equivProd.symm

private instance (H : Subgroup M12Mod) : Finite ↥H :=
  Finite.of_injective (Subtype.val : H → M12Mod) fun _ _ h => Subtype.ext h

private def proj : M12Mod →* Multiplicative (ZMod 2 × ZMod 2) where
  toFun g := Multiplicative.ofAdd ((g.i.val : ZMod 2), (g.j.val : ZMod 2))
  map_one' := by decide +kernel
  map_mul' := by
    rintro ⟨a, b, i, j⟩ ⟨c, d, k, l⟩
    decide +kernel +revert

private def mA : Subgroup M12Mod := baseGrp M12Mod.mx₁ M12Mod.mx₂

private def mE : Subgroup M12Mod :=
  Subgroup.closure ({M12Mod.mx₁, M12Mod.mx₂, M12Mod.mtau} : Set M12Mod)

private def mF : Subgroup M12Mod := fourGrp M12Mod.mx₁ M12Mod.mx₂

private def mz : M12Mod := ⟨2, 2, 0, 0⟩

private def sA : Subgroup M12Mod where
  carrier := {g | g.i = 0 ∧ g.j = 0}
  one_mem' := by decide +kernel
  mul_mem' := by
    rintro ⟨a, b, i, j⟩ ⟨c, d, k, l⟩ hx hy
    have hx' : i = 0 ∧ j = 0 := hx
    have hy' : k = 0 ∧ l = 0 := hy
    obtain ⟨rfl, rfl⟩ := hx'
    obtain ⟨rfl, rfl⟩ := hy'
    decide +kernel +revert
  inv_mem' := by
    rintro ⟨a, b, i, j⟩ hx
    have hx' : i = 0 ∧ j = 0 := hx
    obtain ⟨rfl, rfl⟩ := hx'
    decide +kernel +revert

private def sE : Subgroup M12Mod where
  carrier := {g | g.i = 0}
  one_mem' := by decide +kernel
  mul_mem' := by
    rintro ⟨a, b, i, j⟩ ⟨c, d, k, l⟩ hx hy
    have hx' : i = 0 := hx
    have hy' : k = 0 := hy
    obtain rfl := hx'
    obtain rfl := hy'
    decide +kernel +revert
  inv_mem' := by
    rintro ⟨a, b, i, j⟩ hx
    have hx' : i = 0 := hx
    obtain rfl := hx'
    decide +kernel +revert

private def sF : Subgroup M12Mod where
  carrier := {g | g.i = 0 ∧ g.j = 0 ∧ Even g.a.val ∧ Even g.b.val}
  one_mem' := by decide +kernel
  mul_mem' := by
    rintro ⟨a, b, i, j⟩ ⟨c, d, k, l⟩ hx hy
    have hx' : i = 0 ∧ j = 0 ∧ Even a.val ∧ Even b.val := hx
    have hy' : k = 0 ∧ l = 0 ∧ Even c.val ∧ Even d.val := hy
    obtain ⟨rfl, rfl, ha, hb⟩ := hx'
    obtain ⟨rfl, rfl, hc, hd⟩ := hy'
    decide +kernel +revert
  inv_mem' := by
    rintro ⟨a, b, i, j⟩ hx
    have hx' : i = 0 ∧ j = 0 ∧ Even a.val ∧ Even b.val := hx
    obtain ⟨rfl, rfl, ha, hb⟩ := hx'
    decide +kernel +revert

private theorem mA_eq_sA : mA = sA := by
  unfold mA baseGrp
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · show (M12Mod.mx₁ : M12Mod).i = 0 ∧ (M12Mod.mx₁ : M12Mod).j = 0
      decide +kernel
    · show (M12Mod.mx₂ : M12Mod).i = 0 ∧ (M12Mod.mx₂ : M12Mod).j = 0
      decide +kernel
  · intro g hg
    obtain ⟨a, b, i, j⟩ := g
    have hg' : i = 0 ∧ j = 0 := hg
    obtain ⟨rfl, rfl⟩ := hg'
    rw [M12Mod.eq_pow_mul (⟨a, b, 0, 0⟩ : M12Mod)]
    simp only [Fin.val_zero, pow_zero, mul_one]
    have h1 : M12Mod.mx₁ ∈ Subgroup.closure ({M12Mod.mx₁, M12Mod.mx₂} : Set M12Mod) :=
      Subgroup.subset_closure (Or.inl rfl)
    have h2 : M12Mod.mx₂ ∈ Subgroup.closure ({M12Mod.mx₁, M12Mod.mx₂} : Set M12Mod) :=
      Subgroup.subset_closure (Or.inr rfl)
    exact mul_mem
      (pow_mem h1 a.val) (pow_mem h2 b.val)

private theorem mE_eq_sE : mE = sE := by
  unfold mE
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · show (M12Mod.mx₁ : M12Mod).i = 0
      decide +kernel
    · show (M12Mod.mx₂ : M12Mod).i = 0
      decide +kernel
    · show (M12Mod.mtau : M12Mod).i = 0
      decide +kernel
  · intro g hg
    obtain ⟨a, b, i, j⟩ := g
    have hg' : i = 0 := hg
    obtain rfl := hg'
    rw [M12Mod.eq_pow_mul (⟨a, b, 0, j⟩ : M12Mod)]
    simp only [Fin.val_zero, pow_zero, mul_one]
    have h1 : M12Mod.mx₁ ∈
        Subgroup.closure ({M12Mod.mx₁, M12Mod.mx₂, M12Mod.mtau} : Set M12Mod) :=
      Subgroup.subset_closure (Or.inl rfl)
    have h2 : M12Mod.mx₂ ∈
        Subgroup.closure ({M12Mod.mx₁, M12Mod.mx₂, M12Mod.mtau} : Set M12Mod) :=
      Subgroup.subset_closure (Or.inr (Or.inl rfl))
    have h3 : M12Mod.mtau ∈
        Subgroup.closure ({M12Mod.mx₁, M12Mod.mx₂, M12Mod.mtau} : Set M12Mod) :=
      Subgroup.subset_closure (Or.inr (Or.inr rfl))
    exact mul_mem
      (mul_mem (pow_mem h1 a.val) (pow_mem h2 b.val))
      (pow_mem h3 j.val)

private theorem mem_mF_of_even (a b : Fin 4) (ha : Even a.val) (hb : Even b.val) :
    (⟨a, b, 0, 0⟩ : M12Mod) ∈ mF := by
  have ha' : a = 0 ∨ a = 2 := by
    obtain ⟨k, hk⟩ := ha
    have := a.isLt
    have hk2 : k < 2 := by omega
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · left; exact Fin.ext (by omega)
    · right; exact Fin.ext (by omega)
  have hb' : b = 0 ∨ b = 2 := by
    obtain ⟨k, hk⟩ := hb
    have := b.isLt
    have hk2 : k < 2 := by omega
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · left; exact Fin.ext (by omega)
    · right; exact Fin.ext (by omega)
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · exact Subgroup.one_mem _
  · rw [show (⟨0, 2, 0, 0⟩ : M12Mod) =
        M12Mod.mx₁ ^ 2 * (M12Mod.mx₁ * M12Mod.mx₂) ^ 2 from by decide +kernel]
    exact mul_mem
      (Subgroup.subset_closure (Or.inl rfl)) (Subgroup.subset_closure (Or.inr rfl))
  · rw [show (⟨2, 0, 0, 0⟩ : M12Mod) = M12Mod.mx₁ ^ 2 from by decide +kernel]
    exact Subgroup.subset_closure (Or.inl rfl)
  · rw [show (⟨2, 2, 0, 0⟩ : M12Mod) = (M12Mod.mx₁ * M12Mod.mx₂) ^ 2 from by decide +kernel]
    exact Subgroup.subset_closure (Or.inr rfl)

private theorem mF_eq_sF : mF = sF := by
  unfold mF fourGrp
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · show (M12Mod.mx₁ ^ 2 : M12Mod).i = 0 ∧ (M12Mod.mx₁ ^ 2 : M12Mod).j = 0 ∧
        Even (M12Mod.mx₁ ^ 2).a.val ∧ Even (M12Mod.mx₁ ^ 2).b.val
      decide +kernel
    · show ((M12Mod.mx₁ * M12Mod.mx₂) ^ 2 : M12Mod).i = 0 ∧
        ((M12Mod.mx₁ * M12Mod.mx₂) ^ 2 : M12Mod).j = 0 ∧
        Even ((M12Mod.mx₁ * M12Mod.mx₂) ^ 2).a.val ∧
        Even ((M12Mod.mx₁ * M12Mod.mx₂) ^ 2).b.val
      decide +kernel
  · intro g hg
    obtain ⟨a, b, i, j⟩ := g
    have hg' : i = 0 ∧ j = 0 ∧ Even a.val ∧ Even b.val := hg
    obtain ⟨rfl, rfl, ha, hb⟩ := hg'
    exact mem_mF_of_even a b ha hb

private theorem mem_mA (a b : Fin 4) (i j : Fin 2) :
    (⟨a, b, i, j⟩ : M12Mod) ∈ mA ↔ i = 0 ∧ j = 0 := by
  rw [mA_eq_sA]
  exact Iff.rfl

private theorem mem_mE (a b : Fin 4) (i j : Fin 2) :
    (⟨a, b, i, j⟩ : M12Mod) ∈ mE ↔ i = 0 := by
  rw [mE_eq_sE]
  exact Iff.rfl

private theorem mem_mF (a b : Fin 4) (i j : Fin 2) :
    (⟨a, b, i, j⟩ : M12Mod) ∈ mF ↔ i = 0 ∧ j = 0 ∧ Even a.val ∧ Even b.val := by
  rw [mF_eq_sF]
  exact Iff.rfl

private theorem proj_eq_one_iff (a b : Fin 4) (i j : Fin 2) :
    proj (⟨a, b, i, j⟩ : M12Mod) = 1 ↔ i = 0 ∧ j = 0 := by
  decide +kernel +revert

private theorem proj_ker_eq : proj.ker = mA := by
  rw [mA_eq_sA]
  ext g
  obtain ⟨a, b, i, j⟩ := g
  rw [MonoidHom.mem_ker, proj_eq_one_iff]
  rfl

private theorem card_target : Nat.card (Multiplicative (ZMod 2 × ZMod 2)) = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_prod]
  norm_num [ZMod.card]

private theorem card_E_mul (E : Subgroup M12Mod) :
    Nat.card E = Nat.card (E ⊓ mA : Subgroup M12Mod) * Nat.card (E.map proj) := by
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((E ⊓ mA : Subgroup M12Mod).subgroupOf E)
  have h1 : Nat.card (↥E ⧸ (E ⊓ mA : Subgroup M12Mod).subgroupOf E) =
      Nat.card (E.map proj) := by
    rw [← Subgroup.index_eq_card]
    show (E ⊓ mA : Subgroup M12Mod).relIndex E = Nat.card (E.map proj)
    rw [Subgroup.inf_relIndex_left E mA, ← proj_ker_eq, Subgroup.relIndex_ker E proj]
  have h2 : Nat.card ↥((E ⊓ mA : Subgroup M12Mod).subgroupOf E) =
      Nat.card (E ⊓ mA : Subgroup M12Mod) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : E ⊓ mA ≤ E)).toEquiv
  rw [h1, h2, mul_comm] at hcard
  exact hcard

private theorem sF_ea (g : sF) : Even g.1.a.val := g.2.2.2.1

private theorem sF_eb (g : sF) : Even g.1.b.val := g.2.2.2.2

private def sFToFin (g : sF) : Fin 2 × Fin 2 :=
  (⟨g.1.a.val / 2, by
      obtain ⟨k, hk⟩ := sF_ea g
      have := g.1.a.isLt
      omega⟩,
    ⟨g.1.b.val / 2, by
      obtain ⟨k, hk⟩ := sF_eb g
      have := g.1.b.isLt
      omega⟩)

private theorem sFToFin_injective : Function.Injective sFToFin := by
  rintro ⟨⟨a, b, i, j⟩, hg⟩ ⟨⟨c, d, k, l⟩, hh⟩ hgh
  have hga : Even a.val := hg.2.2.1
  have hha : Even c.val := hh.2.2.1
  have hgb : Even b.val := hg.2.2.2
  have hhb : Even d.val := hh.2.2.2
  have hic : i = k := by
    have hi : i = 0 := hg.1
    have hk : k = 0 := hh.1
    rw [hi, hk]
  have hjl : j = l := by
    have hj : j = 0 := hg.2.1
    have hl : l = 0 := hh.2.1
    rw [hj, hl]
  have hac : a.val / 2 = c.val / 2 := by
    have := congrArg Prod.fst hgh
    simpa [sFToFin] using this
  have hbd : b.val / 2 = d.val / 2 := by
    have := congrArg Prod.snd hgh
    simpa [sFToFin] using this
  have hae : a.val = c.val := by
    obtain ⟨m, hm⟩ := hga
    obtain ⟨n, hn⟩ := hha
    omega
  have hbe : b.val = d.val := by
    obtain ⟨m, hm⟩ := hgb
    obtain ⟨n, hn⟩ := hhb
    omega
  apply Subtype.ext
  obtain rfl : a = c := Fin.ext hae
  obtain rfl : b = d := Fin.ext hbe
  obtain rfl : i = k := hic
  obtain rfl : j = l := hjl
  rfl

private theorem card_sF_le : Nat.card sF ≤ 4 := by
  have h := Nat.card_le_card_of_injective sFToFin sFToFin_injective
  rw [Nat.card_prod, Nat.card_fin] at h
  omega

private theorem even_of_sq_one (a b : Fin 4) :
    (⟨a, b, 0, 0⟩ : M12Mod) ^ 2 = 1 → Even a.val ∧ Even b.val := by
  decide +kernel +revert

private theorem i_eq_zero_of_comm_y (a b : Fin 4) (i j : Fin 2) :
    M12Mod.mx₁ ^ 2 * (⟨a, b, i, j⟩ : M12Mod) =
      (⟨a, b, i, j⟩ : M12Mod) * M12Mod.mx₁ ^ 2 → i = 0 := by
  decide +kernel +revert

private theorem mE_le_centralizer_mF : mE ≤ Subgroup.centralizer (mF : Set M12Mod) := by
  rw [Subgroup.le_centralizer_iff]
  rw [mF_eq_sF]
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨a, b, i, j⟩ := g
  obtain ⟨c, d, k, l⟩ := h
  have hg' : i = 0 ∧ j = 0 ∧ Even a.val ∧ Even b.val := hg
  have hh' : k = 0 := (mem_mE c d k l).mp hh
  clear hg hh
  decide +kernel +revert

private theorem centralizer_mF_le_mE : Subgroup.centralizer (mF : Set M12Mod) ≤ mE := by
  intro g hg
  rw [mem_mE]
  obtain ⟨a, b, i, j⟩ := g
  have h1 : M12Mod.mx₁ ^ 2 ∈ mF := Subgroup.subset_closure (Or.inl rfl)
  have hcomm := (Subgroup.mem_centralizer_iff.mp hg) _ h1
  exact i_eq_zero_of_comm_y a b i j hcomm

private theorem centralizer_mF : Subgroup.centralizer (mF : Set M12Mod) = mE :=
  le_antisymm centralizer_mF_le_mE mE_le_centralizer_mF

private def oneZero : Multiplicative (ZMod 2 × ZMod 2) :=
  Multiplicative.ofAdd ((1 : ZMod 2), 0)

private theorem proj_eq_oneZero_iff (a b : Fin 4) (i j : Fin 2) :
    proj (⟨a, b, i, j⟩ : M12Mod) = oneZero ↔ i = 1 ∧ j = 0 := by
  decide +kernel +revert

private theorem mem_zpowers_mz_of_comm_one (a b c d : Fin 4)
    (hu2 : (⟨a, b, 1, 0⟩ : M12Mod) ^ 2 = 1)
    (hx2 : (⟨c, d, 0, 0⟩ : M12Mod) ^ 2 = 1)
    (hcomm : (⟨a, b, 1, 0⟩ : M12Mod) * ⟨c, d, 0, 0⟩ =
      ⟨c, d, 0, 0⟩ * (⟨a, b, 1, 0⟩ : M12Mod)) :
    (⟨c, d, 0, 0⟩ : M12Mod) ∈ Subgroup.zpowers mz := by
  have hcase : (c = 0 ∧ d = 0) ∨ (c = 2 ∧ d = 2) := by decide +kernel +revert
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Subgroup.one_mem _
  · exact Subgroup.mem_zpowers_iff.mpr ⟨1, by decide +kernel⟩

private theorem orderOf_mz : orderOf mz = 2 := by
  have h2 : mz ^ 2 = 1 := by decide +kernel
  have hdvd : orderOf mz ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
  have hle : orderOf mz ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hne : orderOf mz ≠ 1 := by
    intro h
    exact (by decide +kernel : mz ≠ 1) (orderOf_eq_one_iff.mp h)
  have hpos : 0 < orderOf mz := orderOf_pos mz
  omega

private theorem model_card_le_eight (E : Subgroup M12Mod) (hE : IsElemAbelian 2 E) :
    Nat.card E ≤ 8 := by
  have hEA4 : Nat.card (E ⊓ mA : Subgroup M12Mod) ≤ 4 := by
    have hle : E ⊓ mA ≤ mF := by
      intro x hx
      obtain ⟨a, b, i, j⟩ := x
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxE, hxmA⟩ := hx
      have hxA : i = 0 ∧ j = 0 := (mem_mA a b i j).mp hxmA
      obtain ⟨rfl, rfl⟩ := hxA
      rw [mem_mF]
      exact ⟨rfl, rfl, (even_of_sq_one a b (hE.2 _ hxE)).1,
        (even_of_sq_one a b (hE.2 _ hxE)).2⟩
    calc Nat.card (E ⊓ mA : Subgroup M12Mod) ≤ Nat.card mF := Subgroup.card_le_of_le hle
      _ ≤ 4 := by rw [mF_eq_sF]; exact card_sF_le
  have hP4 : Nat.card (E.map proj) ≤ 4 := by
    calc Nat.card (E.map proj) ≤ Nat.card (Multiplicative (ZMod 2 × ZMod 2)) :=
          Subgroup.card_le_card_group _
      _ = 4 := card_target
  have hmain := card_E_mul E
  by_cases h4 : Nat.card (E.map proj) = 4
  · have htop : E.map proj = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h4, card_target])
    have hmem : oneZero ∈ E.map proj := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨u, huE, hu⟩ := Subgroup.mem_map.mp hmem
    obtain ⟨ua, ub, ui, uj⟩ := u
    have hui : ui = 1 ∧ uj = 0 := (proj_eq_oneZero_iff ua ub ui uj).mp hu
    obtain ⟨rfl, rfl⟩ := hui
    have hEA2 : Nat.card (E ⊓ mA : Subgroup M12Mod) ≤ 2 := by
      have hle : E ⊓ mA ≤ Subgroup.zpowers mz := by
        intro x hx
        obtain ⟨a, b, i, j⟩ := x
        rw [Subgroup.mem_inf] at hx
        obtain ⟨hxE, hxmA⟩ := hx
        have hxA : i = 0 ∧ j = 0 := (mem_mA a b i j).mp hxmA
        obtain ⟨rfl, rfl⟩ := hxA
        have hx2 : (⟨a, b, 0, 0⟩ : M12Mod) ^ 2 = 1 := hE.2 _ hxE
        have hu2 : (⟨ua, ub, 1, 0⟩ : M12Mod) ^ 2 = 1 := hE.2 _ huE
        have hcomm : (⟨ua, ub, 1, 0⟩ : M12Mod) * (⟨a, b, 0, 0⟩ : M12Mod) =
            (⟨a, b, 0, 0⟩ : M12Mod) * (⟨ua, ub, 1, 0⟩ : M12Mod) := by
          have := congrArg Subtype.val (hE.1.is_comm.comm
            ⟨(⟨ua, ub, 1, 0⟩ : M12Mod), huE⟩ ⟨(⟨a, b, 0, 0⟩ : M12Mod), hxE⟩)
          simpa using this
        exact mem_zpowers_mz_of_comm_one ua ub a b hu2 hx2 hcomm
      calc Nat.card (E ⊓ mA : Subgroup M12Mod) ≤ Nat.card (Subgroup.zpowers mz) :=
            Subgroup.card_le_of_le hle
        _ = orderOf mz := Nat.card_zpowers mz
        _ = 2 := orderOf_mz
    calc Nat.card E = Nat.card (E ⊓ mA : Subgroup M12Mod) * Nat.card (E.map proj) := hmain
      _ ≤ 2 * 4 := Nat.mul_le_mul hEA2 (le_of_eq h4)
      _ = 8 := by norm_num
  · have hdvd : Nat.card (E.map proj) ∣ 4 := by
      rw [← card_target]
      exact Subgroup.card_subgroup_dvd_card (E.map proj)
    have hP2 : Nat.card (E.map proj) ≤ 2 := by
      obtain ⟨k, hk, hdk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (by
        show Nat.card (E.map proj) ∣ 2 ^ 2
        norm_num
        exact hdvd)
      have hk1 : k ≤ 1 := by
        by_contra h
        push Not at h
        have hk2 : k = 2 := by omega
        subst hk2
        norm_num [pow_two] at hdk
        exact h4 hdk
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl
      · norm_num at hdk ⊢
        omega
      · norm_num at hdk ⊢
        omega
    calc Nat.card E = Nat.card (E ⊓ mA : Subgroup M12Mod) * Nat.card (E.map proj) := hmain
      _ ≤ 4 * 2 := Nat.mul_le_mul hEA4 hP2
      _ = 8 := by norm_num

private def oneOne : Multiplicative (ZMod 2 × ZMod 2) :=
  Multiplicative.ofAdd ((0 : ZMod 2), 1)

private def zeroOne : Multiplicative (ZMod 2 × ZMod 2) :=
  Multiplicative.ofAdd ((0 : ZMod 2), (1 : ZMod 2))

private theorem orderOf_oneOne : orderOf oneOne = 2 := by
  have h2 : oneOne ^ 2 = 1 := by decide +kernel
  have hdvd : orderOf oneOne ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
  have hle : orderOf oneOne ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hne : orderOf oneOne ≠ 1 := by
    intro h
    exact (by decide +kernel : oneOne ≠ 1) (orderOf_eq_one_iff.mp h)
  have hpos : 0 < orderOf oneOne := orderOf_pos oneOne
  omega

private theorem proj_zero_i (a b : Fin 4) (j : Fin 2) :
    proj (⟨a, b, 0, j⟩ : M12Mod) = 1 ∨
      proj (⟨a, b, 0, j⟩ : M12Mod) = oneOne := by
  decide +kernel +revert

private theorem map_mE_eq : mE.map proj = Subgroup.zpowers oneOne := by
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨a, b, i, j⟩ := x
    have hi : i = 0 := (mem_mE a b i j).mp hx
    subst hi
    rcases proj_zero_i a b j with h1 | h1
    · rw [h1]; exact Subgroup.one_mem _
    · rw [h1]; exact Subgroup.mem_zpowers oneOne
  · intro y hy
    have h1 : oneOne ∈ mE.map proj := by
      refine Subgroup.mem_map.mpr ⟨M12Mod.mtau, ?_, ?_⟩
      · exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
      · decide +kernel
    exact (Subgroup.zpowers_le.mpr h1) hy

private theorem card_map_proj_le_two : Nat.card (mE.map proj) ≤ 2 := by
  rw [map_mE_eq, Nat.card_zpowers, orderOf_oneOne]

private theorem card_mF_le : Nat.card mF ≤ 4 := by
  rw [mF_eq_sF]
  exact card_sF_le

private def sZ : Subgroup M12Mod where
  carrier := {g | g = 1 ∨ g = mz}
  one_mem' := by decide +kernel
  mul_mem' := by
    rintro x y hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide +kernel
  inv_mem' := by
    rintro x hx
    rcases hx with rfl | rfl <;> decide +kernel

private theorem zpowers_mz_eq_sZ : Subgroup.zpowers mz = sZ := by
  refine le_antisymm ?_ ?_
  · exact Subgroup.zpowers_le.mpr (Or.inr rfl)
  · intro x hx
    have hx' : x = 1 ∨ x = mz := hx
    rcases hx' with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers mz

private theorem card_sZ : Nat.card sZ = 2 := by
  rw [← zpowers_mz_eq_sZ, Nat.card_zpowers, orderOf_mz]

private theorem mz_mem_mF : mz ∈ mF :=
  (mem_mF 2 2 0 0).mpr ⟨rfl, rfl, by decide +kernel, by decide +kernel⟩

private def quad (u : M12Mod) : Finset M12Mod :=
  {1, M12Mod.mx₁ ^ 2, mz, M12Mod.mx₁ ^ 2 * mz, u,
    M12Mod.mx₁ ^ 2 * u, mz * u, M12Mod.mx₁ ^ 2 * mz * u}

private def triple (u v : M12Mod) : Finset M12Mod :=
  {1, mz, u, v, mz * u, mz * v, u * v, mz * u * v}

private theorem quad_subset {E : Subgroup M12Mod} {u : M12Mod}
    (hy : M12Mod.mx₁ ^ 2 ∈ E) (hz : mz ∈ E) (hu : u ∈ E) :
    ∀ g ∈ quad u, g ∈ E := by
  intro g hg
  simp only [quad, Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact hy
  · exact hz
  · exact mul_mem hy hz
  · exact hu
  · exact mul_mem hy hu
  · exact mul_mem hz hu
  · exact mul_mem (mul_mem hy hz) hu

private theorem triple_subset {E : Subgroup M12Mod} {u v : M12Mod}
    (hu : u ∈ E) (hv : v ∈ E) (hz : mz ∈ E) :
    ∀ g ∈ triple u v, g ∈ E := by
  intro g hg
  simp only [triple, Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact hz
  · exact hu
  · exact hv
  · exact mul_mem hz hu
  · exact mul_mem hz hv
  · exact mul_mem hu hv
  · exact mul_mem (mul_mem hz hu) hv

private theorem mem_quad_of_comm (p q ga gb : Fin 4) (gi gj : Fin 2)
    (hy : M12Mod.mx₁ ^ 2 * (⟨ga, gb, gi, gj⟩ : M12Mod) =
      (⟨ga, gb, gi, gj⟩ : M12Mod) * M12Mod.mx₁ ^ 2)
    (hz : mz * (⟨ga, gb, gi, gj⟩ : M12Mod) = (⟨ga, gb, gi, gj⟩ : M12Mod) * mz)
    (hu : (⟨p, q, 0, 1⟩ : M12Mod) * (⟨ga, gb, gi, gj⟩ : M12Mod) =
      (⟨ga, gb, gi, gj⟩ : M12Mod) * (⟨p, q, 0, 1⟩ : M12Mod)) :
    (⟨ga, gb, gi, gj⟩ : M12Mod) ∈ quad (⟨p, q, 0, 1⟩ : M12Mod) := by
  decide +kernel +revert

private theorem mem_triple_of_comm (a b p q ga gb : Fin 4) (gi gj : Fin 2)
    (hu2 : (⟨a, b, 1, 0⟩ : M12Mod) ^ 2 = 1)
    (hcomm : (⟨a, b, 1, 0⟩ : M12Mod) * (⟨p, q, 0, 1⟩ : M12Mod) =
      (⟨p, q, 0, 1⟩ : M12Mod) * (⟨a, b, 1, 0⟩ : M12Mod))
    (hu : (⟨a, b, 1, 0⟩ : M12Mod) * (⟨ga, gb, gi, gj⟩ : M12Mod) =
      (⟨ga, gb, gi, gj⟩ : M12Mod) * (⟨a, b, 1, 0⟩ : M12Mod))
    (hv : (⟨p, q, 0, 1⟩ : M12Mod) * (⟨ga, gb, gi, gj⟩ : M12Mod) =
      (⟨ga, gb, gi, gj⟩ : M12Mod) * (⟨p, q, 0, 1⟩ : M12Mod)) :
    (⟨ga, gb, gi, gj⟩ : M12Mod) ∈
      triple (⟨a, b, 1, 0⟩ : M12Mod) (⟨p, q, 0, 1⟩ : M12Mod) := by
  decide +kernel +revert

private theorem mem_zpowers_mz_of_comm_one_i_one (a b c d : Fin 4) (j : Fin 2)
    (hu2 : (⟨a, b, 1, j⟩ : M12Mod) ^ 2 = 1)
    (hx2 : (⟨c, d, 0, 0⟩ : M12Mod) ^ 2 = 1)
    (hcomm : (⟨a, b, 1, j⟩ : M12Mod) * ⟨c, d, 0, 0⟩ =
      ⟨c, d, 0, 0⟩ * (⟨a, b, 1, j⟩ : M12Mod)) :
    (⟨c, d, 0, 0⟩ : M12Mod) ∈ Subgroup.zpowers mz := by
  have hcase : (c = 0 ∧ d = 0) ∨ (c = 2 ∧ d = 2) := by decide +kernel +revert
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Subgroup.one_mem _
  · exact Subgroup.mem_zpowers_iff.mpr ⟨1, by decide +kernel⟩

private theorem proj_eq_zeroOne_iff (a b : Fin 4) (i j : Fin 2) :
    proj (⟨a, b, i, j⟩ : M12Mod) = zeroOne ↔ i = 0 ∧ j = 1 := by
  decide +kernel +revert

private theorem model_centralizer_eq_eight (E : Subgroup M12Mod) (hE : IsElemAbelian 2 E)
    (h8 : Nat.card E = 8) :
    Subgroup.centralizer (E : Set M12Mod) = E := by
  refine le_antisymm ?_ ?_
  · intro g hg
    obtain ⟨ga, gb, gi, gj⟩ := g
    by_cases hsub : E ≤ mE
    · have hEAle_mF : E ⊓ mA ≤ mF := by
        intro x hx
        rw [Subgroup.mem_inf] at hx
        obtain ⟨hxE, hxmA⟩ := hx
        obtain ⟨a, b, i, j⟩ := x
        have hxA : i = 0 ∧ j = 0 := (mem_mA a b i j).mp hxmA
        obtain ⟨rfl, rfl⟩ := hxA
        rw [mem_mF]
        exact ⟨rfl, rfl, (even_of_sq_one a b (hE.2 _ hxE)).1,
          (even_of_sq_one a b (hE.2 _ hxE)).2⟩
      have hpi2 : Nat.card (E.map proj) ≤ 2 :=
        (Subgroup.card_le_of_le (Subgroup.map_mono hsub)).trans card_map_proj_le_two
      have hcardEA : Nat.card (E ⊓ mA : Subgroup M12Mod) = 4 := by
        have hmain := card_E_mul E
        have hEA_le : Nat.card (E ⊓ mA : Subgroup M12Mod) ≤ 4 :=
          (Subgroup.card_le_of_le hEAle_mF).trans card_mF_le
        have hb : Nat.card (E.map proj) = 1 ∨ Nat.card (E.map proj) = 2 := by
          have := Nat.card_pos (α := E.map proj)
          omega
        rcases hb with hb | hb
        · rw [hb, mul_one] at hmain
          omega
        · rw [hb] at hmain
          omega
      have hEA : E ⊓ mA = mF := by
        refine Subgroup.eq_of_le_of_card_ge hEAle_mF ?_
        rw [hcardEA]
        exact card_mF_le
      have hmF_le_E : mF ≤ E := hEA ▸ inf_le_left
      have hnotE : ¬ E ≤ mA := by
        intro h
        have hEmA : E ⊓ mA = E := inf_eq_left.mpr h
        have : Nat.card E ≤ 4 := by
          rw [← hEmA, hEA]
          exact card_mF_le
        omega
      obtain ⟨u, huE, huA⟩ := Set.not_subset.mp hnotE
      obtain ⟨ua, ub, ui, uj⟩ := u
      have huE' : (⟨ua, ub, ui, uj⟩ : M12Mod) ∈ E := huE
      have hu_i : ui = 0 := (mem_mE ua ub ui uj).mp (hsub huE')
      have hu_j : uj = 1 := by
        have hne : uj.val ≠ 0 := by
          intro h
          apply huA
          exact (mem_mA ua ub ui uj).mpr ⟨hu_i, Fin.ext (by simpa using h)⟩
        have := uj.isLt
        exact Fin.ext (by omega)
      subst hu_i
      subst hu_j
      have hyE : M12Mod.mx₁ ^ 2 ∈ E :=
        hmF_le_E (Subgroup.subset_closure (Or.inl rfl))
      have hzE : mz ∈ E := hmF_le_E mz_mem_mF
      have hyg : M12Mod.mx₁ ^ 2 * (⟨ga, gb, gi, gj⟩ : M12Mod) =
          (⟨ga, gb, gi, gj⟩ : M12Mod) * M12Mod.mx₁ ^ 2 :=
        (Subgroup.mem_centralizer_iff.mp hg) _ hyE
      have hzg : mz * (⟨ga, gb, gi, gj⟩ : M12Mod) =
          (⟨ga, gb, gi, gj⟩ : M12Mod) * mz :=
        (Subgroup.mem_centralizer_iff.mp hg) _ hzE
      have hug : (⟨ua, ub, 0, 1⟩ : M12Mod) * (⟨ga, gb, gi, gj⟩ : M12Mod) =
          (⟨ga, gb, gi, gj⟩ : M12Mod) * (⟨ua, ub, 0, 1⟩ : M12Mod) :=
        (Subgroup.mem_centralizer_iff.mp hg) _ huE'
      exact quad_subset hyE hzE huE' _
        (mem_quad_of_comm ua ub ga gb gi gj hyg hzg hug)
    · obtain ⟨u0, hu0E, hu0_notmE⟩ := Set.not_subset.mp hsub
      obtain ⟨u0a, u0b, u0i, u0j⟩ := u0
      have hu0_i : u0i = 1 := by
        have hne : u0i.val ≠ 0 := by
          intro h
          apply hu0_notmE
          exact (mem_mE u0a u0b u0i u0j).mpr (Fin.ext (by simpa using h))
        have := u0i.isLt
        exact Fin.ext (by omega)
      subst hu0_i
      have hu0E' : (⟨u0a, u0b, 1, u0j⟩ : M12Mod) ∈ E := hu0E
      have hEAle : E ⊓ mA ≤ Subgroup.zpowers mz := by
        intro x hx
        rw [Subgroup.mem_inf] at hx
        obtain ⟨hxE, hxmA⟩ := hx
        obtain ⟨c, d, i, j⟩ := x
        have hxA : i = 0 ∧ j = 0 := (mem_mA c d i j).mp hxmA
        obtain ⟨rfl, rfl⟩ := hxA
        have hx2 : (⟨c, d, 0, 0⟩ : M12Mod) ^ 2 = 1 := hE.2 _ hxE
        have hu2 : (⟨u0a, u0b, 1, u0j⟩ : M12Mod) ^ 2 = 1 := hE.2 _ hu0E'
        have hcomm : (⟨u0a, u0b, 1, u0j⟩ : M12Mod) * (⟨c, d, 0, 0⟩ : M12Mod) =
            (⟨c, d, 0, 0⟩ : M12Mod) * (⟨u0a, u0b, 1, u0j⟩ : M12Mod) := by
          have := congrArg Subtype.val (hE.1.is_comm.comm
            ⟨(⟨u0a, u0b, 1, u0j⟩ : M12Mod), hu0E'⟩ ⟨(⟨c, d, 0, 0⟩ : M12Mod), hxE⟩)
          simpa using this
        exact mem_zpowers_mz_of_comm_one_i_one u0a u0b c d u0j hu2 hx2 hcomm
      have hEA_ne_bot : E ⊓ mA ≠ ⊥ := by
        intro hbot
        have hinj : Function.Injective (fun x : E => proj x.1) := by
          intro x y hxy
          have hxy' : proj x.1 = proj y.1 := hxy
          have h1 : proj (x.1 * y.1⁻¹) = 1 := by
            rw [map_mul, map_inv, hxy']
            exact mul_inv_cancel (proj y.1)
          have h2 : x.1 * y.1⁻¹ ∈ mA := by
            rw [← proj_ker_eq, MonoidHom.mem_ker]
            exact h1
          have h3 : x.1 * y.1⁻¹ ∈ E ⊓ mA :=
            ⟨E.mul_mem x.2 (E.inv_mem y.2), h2⟩
          rw [hbot] at h3
          have h4 : x.1 * y.1⁻¹ = 1 := Subgroup.mem_bot.mp h3
          apply Subtype.ext
          exact mul_inv_eq_one.mp h4
        have hle := Nat.card_le_card_of_injective _ hinj
        rw [card_target] at hle
        omega
      have hEAle_sZ : E ⊓ mA ≤ sZ := by
        rw [← zpowers_mz_eq_sZ]
        exact hEAle
      have hzEA : mz ∈ E ⊓ mA := by
        obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEA_ne_bot
        have ha_sZ : (a : M12Mod) ∈ sZ := hEAle_sZ a.2
        have ha_cases : (a : M12Mod) = 1 ∨ (a : M12Mod) = mz := ha_sZ
        rcases ha_cases with h1 | h1
        · exfalso
          exact ha (Subtype.ext h1)
        · rw [← h1]
          exact a.2
      have hzE : mz ∈ E := hzEA.1
      have hsZ_le_EA : sZ ≤ E ⊓ mA := by
        intro x hx
        have hx' : x = 1 ∨ x = mz := hx
        rcases hx' with rfl | rfl
        · exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
        · exact hzEA
      have hcardEA : Nat.card (E ⊓ mA : Subgroup M12Mod) = 2 := by
        apply le_antisymm
        · calc Nat.card (E ⊓ mA : Subgroup M12Mod) ≤ Nat.card sZ :=
              Subgroup.card_le_of_le hEAle_sZ
            _ = 2 := card_sZ
        · calc 2 = Nat.card sZ := card_sZ.symm
            _ ≤ Nat.card (E ⊓ mA : Subgroup M12Mod) := Subgroup.card_le_of_le hsZ_le_EA
      have hpi_eq : Nat.card (E.map proj) = 4 := by
        have hmain := card_E_mul E
        rw [hcardEA] at hmain
        omega
      have htop : E.map proj = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (by rw [hpi_eq, card_target])
      obtain ⟨u, huE, hu⟩ := Subgroup.mem_map.mp (by
        rw [htop]; exact Subgroup.mem_top oneZero)
      obtain ⟨ua, ub, ui, uj⟩ := u
      have hui : ui = 1 ∧ uj = 0 := (proj_eq_oneZero_iff ua ub ui uj).mp hu
      obtain ⟨rfl, rfl⟩ := hui
      obtain ⟨v, hvE, hv⟩ := Subgroup.mem_map.mp (by
        rw [htop]; exact Subgroup.mem_top zeroOne)
      obtain ⟨va, vb, vi, vj⟩ := v
      have hvj : vi = 0 ∧ vj = 1 := (proj_eq_zeroOne_iff va vb vi vj).mp hv
      obtain ⟨rfl, rfl⟩ := hvj
      have hu2 : (⟨ua, ub, 1, 0⟩ : M12Mod) ^ 2 = 1 := hE.2 _ huE
      have hcomm : (⟨ua, ub, 1, 0⟩ : M12Mod) * (⟨va, vb, 0, 1⟩ : M12Mod) =
          (⟨va, vb, 0, 1⟩ : M12Mod) * (⟨ua, ub, 1, 0⟩ : M12Mod) := by
        have := congrArg Subtype.val (hE.1.is_comm.comm
          ⟨(⟨ua, ub, 1, 0⟩ : M12Mod), huE⟩ ⟨(⟨va, vb, 0, 1⟩ : M12Mod), hvE⟩)
        simpa using this
      have hug : (⟨ua, ub, 1, 0⟩ : M12Mod) * (⟨ga, gb, gi, gj⟩ : M12Mod) =
          (⟨ga, gb, gi, gj⟩ : M12Mod) * (⟨ua, ub, 1, 0⟩ : M12Mod) :=
        (Subgroup.mem_centralizer_iff.mp hg) _ huE
      have hvg : (⟨va, vb, 0, 1⟩ : M12Mod) * (⟨ga, gb, gi, gj⟩ : M12Mod) =
          (⟨ga, gb, gi, gj⟩ : M12Mod) * (⟨va, vb, 0, 1⟩ : M12Mod) :=
        (Subgroup.mem_centralizer_iff.mp hg) _ hvE
      exact triple_subset huE hvE hzE _
        (mem_triple_of_comm ua ub va vb ga gb gi gj hu2 hcomm hug hvg)
  · letI : IsMulCommutative ↥E := hE.1
    exact Subgroup.le_centralizer E

private theorem sq_mul_conj_ne_one (a b : Fin 4) (i j : Fin 2)
    (hx2 : (⟨a, b, i, j⟩ : M12Mod) ^ 2 = 1) (hi : i = 1) :
    ((⟨a, b, i, j⟩ : M12Mod) *
      (M12Mod.mx₁ * (⟨a, b, i, j⟩ : M12Mod) * M12Mod.mx₁⁻¹)) ^ 2 ≠ 1 := by
  decide +kernel +revert

private theorem x1_conj_mul_T (a b : Fin 4) (i j : Fin 2) (hi : i = 0) (hj : j = 1) :
    M12Mod.mx₁ * (⟨a, b, i, j⟩ : M12Mod) * M12Mod.mx₁⁻¹ * (⟨a, b, i, j⟩ : M12Mod) =
      M12Mod.mx₁ ^ 2 := by
  decide +kernel +revert

private theorem mF_case (h : M12Mod) (hh : h ∈ mF) (hh1 : h ≠ 1) :
    h = M12Mod.mx₁ ^ 2 ∨ h = M12Mod.mx₁ ^ 2 * mz ∨ h = mz := by
  rw [mem_mF] at hh
  obtain ⟨a, b, i, j⟩ := h
  obtain ⟨hi, hj, ha, hb⟩ := hh
  subst hi; subst hj
  have ha' : a = 0 ∨ a = 2 := by
    fin_cases a
    · left; rfl
    · exfalso; norm_num at ha
    · right; rfl
    · exfalso; norm_num at ha
  have hb' : b = 0 ∨ b = 2 := by
    fin_cases b
    · left; rfl
    · exfalso; norm_num at hb
    · right; rfl
    · exfalso; norm_num at hb
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · exact absurd rfl hh1
  · right; left; decide +kernel
  · left; decide +kernel
  · right; right; decide +kernel

private theorem model_fourGrp_le_of_normal_elemAbelian (E : Subgroup M12Mod)
    (hE : IsElemAbelian 2 E) (hN : NormalIn E ⊤) (h4 : 4 ≤ Nat.card E) :
    mF ≤ E ∧ E ≤ Subgroup.centralizer (mF : Set M12Mod) := by
  have hEmE : E ≤ mE := by
    intro x hx
    obtain ⟨a, b, i, j⟩ := x
    rw [mem_mE]
    by_contra hi
    have hi1 : i = 1 := by
      have : i.val ≠ 0 := fun h => hi (Fin.ext (by simpa using h))
      have := i.isLt
      exact Fin.ext (by omega)
    have hy : M12Mod.mx₁ * (⟨a, b, i, j⟩ : M12Mod) * M12Mod.mx₁⁻¹ ∈ E :=
      hN.2 M12Mod.mx₁ (Subgroup.mem_top _) _ hx
    have hxy : (⟨a, b, i, j⟩ : M12Mod) *
        (M12Mod.mx₁ * (⟨a, b, i, j⟩ : M12Mod) * M12Mod.mx₁⁻¹) ∈ E :=
      mul_mem hx hy
    have hsq : ((⟨a, b, i, j⟩ : M12Mod) *
        (M12Mod.mx₁ * (⟨a, b, i, j⟩ : M12Mod) * M12Mod.mx₁⁻¹)) ^ 2 = 1 := hE.2 _ hxy
    have hx2 : (⟨a, b, i, j⟩ : M12Mod) ^ 2 = 1 := hE.2 _ hx
    exact sq_mul_conj_ne_one a b i j hx2 hi1 hsq
  have hEA_le_mF : E ⊓ mA ≤ mF := by
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxE, hxmA⟩ := hx
    obtain ⟨a, b, i, j⟩ := x
    have hxA : i = 0 ∧ j = 0 := (mem_mA a b i j).mp hxmA
    obtain ⟨rfl, rfl⟩ := hxA
    rw [mem_mF]
    exact ⟨rfl, rfl, (even_of_sq_one a b (hE.2 _ hxE)).1,
      (even_of_sq_one a b (hE.2 _ hxE)).2⟩
  have hpi2 : Nat.card (E.map proj) ≤ 2 :=
    (Subgroup.card_le_of_le (Subgroup.map_mono hEmE)).trans card_map_proj_le_two
  have hcard2 : 2 ≤ Nat.card (E ⊓ mA : Subgroup M12Mod) := by
    have hmain := card_E_mul E
    have hpos : 0 < Nat.card (E.map proj) := Nat.card_pos
    have hb : Nat.card (E.map proj) = 1 ∨ Nat.card (E.map proj) = 2 := by omega
    rcases hb with hb | hb <;> rw [hb] at hmain <;> omega
  have hEA_ne_bot : E ⊓ mA ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard2
    omega
  obtain ⟨h, hh1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEA_ne_bot
  have hhEA : (h : M12Mod) ∈ E ⊓ mA := h.2
  have hh_mF : (h : M12Mod) ∈ mF := hEA_le_mF hhEA
  have hhE : (h : M12Mod) ∈ E := hhEA.1
  have hh1' : (h : M12Mod) ≠ 1 := fun hh => hh1 (Subtype.ext hh)
  have hzE : mz ∈ E := by
    have hcase := mF_case (h : M12Mod) hh_mF hh1'
    rcases hcase with hy' | hyz' | hz'
    · have hconj : M12Mod.mlam * (h : M12Mod) * M12Mod.mlam⁻¹ ∈ E :=
        hN.2 M12Mod.mlam (Subgroup.mem_top _) _ hhE
      rw [hy'] at hconj
      rw [hy'] at hhE
      have hval : M12Mod.mlam * M12Mod.mx₁ ^ 2 * M12Mod.mlam⁻¹ =
          M12Mod.mx₁ ^ 2 * mz := by
        decide +kernel
      rw [hval] at hconj
      have hprod : M12Mod.mx₁ ^ 2 * (M12Mod.mx₁ ^ 2 * mz) ∈ E := mul_mem hhE hconj
      have heq : M12Mod.mx₁ ^ 2 * (M12Mod.mx₁ ^ 2 * mz) = mz := by decide +kernel
      rwa [heq] at hprod
    · have hconj : M12Mod.mlam * (h : M12Mod) * M12Mod.mlam⁻¹ ∈ E :=
        hN.2 M12Mod.mlam (Subgroup.mem_top _) _ hhE
      rw [hyz'] at hconj
      rw [hyz'] at hhE
      have hval : M12Mod.mlam * (M12Mod.mx₁ ^ 2 * mz) * M12Mod.mlam⁻¹ =
          M12Mod.mx₁ ^ 2 := by
        decide +kernel
      rw [hval] at hconj
      have hprod : M12Mod.mx₁ ^ 2 * mz * M12Mod.mx₁ ^ 2 ∈ E := mul_mem hhE hconj
      have heq : M12Mod.mx₁ ^ 2 * mz * M12Mod.mx₁ ^ 2 = mz := by decide +kernel
      rwa [heq] at hprod
    · exact hz' ▸ hhE
  have hyE : M12Mod.mx₁ ^ 2 ∈ E := by
    by_cases hEA4 : Nat.card (E ⊓ mA : Subgroup M12Mod) = 4
    · have hEA_eq : E ⊓ mA = mF := by
        refine Subgroup.eq_of_le_of_card_ge hEA_le_mF ?_
        rw [hEA4]
        exact card_mF_le
      have hmF_le_E : mF ≤ E := hEA_eq ▸ inf_le_left
      exact hmF_le_E (Subgroup.subset_closure (Or.inl rfl))
    · have hnotA : ¬ E ≤ mA := by
        intro h
        have hE_mF : E ≤ mF := fun x hx => hEA_le_mF ⟨hx, h hx⟩
        have hE4 : Nat.card E ≤ 4 := (Subgroup.card_le_of_le hE_mF).trans card_mF_le
        have hEmA : E ⊓ mA = E := inf_eq_left.mpr h
        rw [hEmA] at hEA4
        omega
      obtain ⟨u, huE, huA⟩ := Set.not_subset.mp hnotA
      obtain ⟨ua, ub, ui, uj⟩ := u
      have hu_mE : ui = 0 := (mem_mE ua ub ui uj).mp (hEmE huE)
      have hu_j : uj = 1 := by
        have hne : uj.val ≠ 0 := by
          intro hh
          apply huA
          exact (mem_mA ua ub ui uj).mpr ⟨hu_mE, Fin.ext (by simpa using hh)⟩
        have := uj.isLt
        exact Fin.ext (by omega)
      have hconj : M12Mod.mx₁ * (⟨ua, ub, ui, uj⟩ : M12Mod) * M12Mod.mx₁⁻¹ ∈ E :=
        hN.2 M12Mod.mx₁ (Subgroup.mem_top _) _ huE
      have hprod : M12Mod.mx₁ * (⟨ua, ub, ui, uj⟩ : M12Mod) * M12Mod.mx₁⁻¹ *
          (⟨ua, ub, ui, uj⟩ : M12Mod) ∈ E := mul_mem hconj huE
      have heq : M12Mod.mx₁ * (⟨ua, ub, ui, uj⟩ : M12Mod) * M12Mod.mx₁⁻¹ *
          (⟨ua, ub, ui, uj⟩ : M12Mod) = M12Mod.mx₁ ^ 2 :=
        x1_conj_mul_T ua ub ui uj hu_mE hu_j
      rw [heq] at hprod
      exact hprod
  have hmF_le_E : mF ≤ E := by
    unfold mF fourGrp
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hyE
    · have heq : (M12Mod.mx₁ * M12Mod.mx₂) ^ 2 = mz := by decide +kernel
      rw [heq]
      exact hzE
  exact ⟨hmF_le_E, by rw [centralizer_mF]; exact hEmE⟩

private def sE8 : Subgroup M12Mod where
  carrier := {g | g.i = 0 ∧ Even g.a.val ∧ Even g.b.val}
  one_mem' := by exact ⟨rfl, by decide, by decide⟩
  mul_mem' := by
    rintro x y hx hy
    obtain ⟨a, b, i, j⟩ := x
    obtain ⟨c, d, k, l⟩ := y
    have hx' : i = 0 ∧ Even a.val ∧ Even b.val := hx
    have hy' : k = 0 ∧ Even c.val ∧ Even d.val := hy
    obtain ⟨rfl, ha, hb⟩ := hx'
    obtain ⟨rfl, hc, hd⟩ := hy'
    clear hx hy
    exact ⟨rfl, by decide +kernel +revert, by decide +kernel +revert⟩
  inv_mem' := by
    rintro x hx
    obtain ⟨a, b, i, j⟩ := x
    have hx' : i = 0 ∧ Even a.val ∧ Even b.val := hx
    obtain ⟨rfl, ha, hb⟩ := hx'
    clear hx
    exact ⟨rfl, by decide +kernel +revert, by decide +kernel +revert⟩

private theorem mem_sE8 (g : M12Mod) :
    g ∈ sE8 ↔ g.i = 0 ∧ Even g.a.val ∧ Even g.b.val := Iff.rfl

private def mE8 : Subgroup M12Mod :=
  Subgroup.closure ({M12Mod.mx₁ ^ 2, (M12Mod.mx₁ * M12Mod.mx₂) ^ 2,
    M12Mod.mtau} : Set M12Mod)

private def mE8b : Subgroup M12Mod :=
  Subgroup.closure ({M12Mod.mx₁ ^ 2, (M12Mod.mx₁ * M12Mod.mx₂) ^ 2,
    M12Mod.mx₁ * M12Mod.mx₂ * M12Mod.mtau} : Set M12Mod)

private theorem mF_le_mE8 : mF ≤ mE8 := by
  unfold mF fourGrp mE8
  rw [Subgroup.closure_le]
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))

private theorem mE8_gen_eq (a b : Fin 4) (j : Fin 2) :
    (⟨a, b, 0, j⟩ : M12Mod) =
      (⟨a, b, 0, 0⟩ : M12Mod) * M12Mod.mtau ^ j.val := by
  decide +kernel +revert

private theorem mE8_eq_sE8 : mE8 = sE8 := by
  refine le_antisymm ?_ ?_
  · unfold mE8
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact (mem_sE8 _).mpr ⟨rfl, by decide +kernel, by decide +kernel⟩
    · exact (mem_sE8 _).mpr ⟨rfl, by decide +kernel, by decide +kernel⟩
    · exact (mem_sE8 _).mpr ⟨rfl, by decide +kernel, by decide +kernel⟩
  · intro x hx
    obtain ⟨a, b, i, j⟩ := x
    rw [mem_sE8] at hx
    obtain ⟨rfl, ha, hb⟩ := hx
    have hA' : (⟨a, b, 0, 0⟩ : M12Mod) ∈ mE8 :=
      mF_le_mE8 (mem_mF_of_even a b ha hb)
    rw [mE8_gen_eq a b j]
    have hmtau : M12Mod.mtau ∈ mE8 :=
      Subgroup.subset_closure (k := ({M12Mod.mx₁ ^ 2, (M12Mod.mx₁ * M12Mod.mx₂) ^ 2,
        M12Mod.mtau} : Set M12Mod)) (Or.inr (Or.inr rfl))
    have hpow : M12Mod.mtau ^ j.val ∈ mE8 := by
      fin_cases j <;> simp [hmtau]
    exact mul_mem hA' hpow

private theorem mF_le_sE8 : mF ≤ sE8 := by
  intro x hx
  rw [mem_mF] at hx
  obtain ⟨a, b, i, j⟩ := x
  obtain ⟨hi, hj, ha, hb⟩ := hx
  exact ⟨hi, ha, hb⟩

private theorem mF_le_mE8b : mF ≤ mE8b := by
  unfold mF fourGrp mE8b
  rw [Subgroup.closure_le]
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))

private theorem even_sub_one_of_odd (a : Fin 4) (ha : Odd a.val) : Even (a - 1).val := by
  have h : a.val = 1 ∨ a.val = 3 := by
    obtain ⟨k, hk⟩ := ha
    have := a.isLt
    omega
  rcases h with h | h
  · have ha1 : a = 1 := Fin.ext h
    subst ha1
    decide +kernel
  · have ha3 : a = 3 := Fin.ext h
    subst ha3
    decide +kernel

private theorem mE8b_gen_eq (a b : Fin 4) (ha : Odd a.val) (hb : Odd b.val) :
    (⟨a, b, 0, 1⟩ : M12Mod) =
      (⟨a - 1, b - 1, 0, 0⟩ : M12Mod) *
        (M12Mod.mx₁ * M12Mod.mx₂ * M12Mod.mtau) := by
  decide +kernel +revert

private theorem zpowers_gen_mem_mE8b {a b : Fin 4} (ha : Odd a.val) (hb : Odd b.val) :
    (⟨a, b, 0, 1⟩ : M12Mod) ∈ mE8b := by
  have hmem : (⟨a - 1, b - 1, 0, 0⟩ : M12Mod) ∈ mF :=
    (mem_mF _ _ 0 0).mpr ⟨rfl, rfl, even_sub_one_of_odd a ha, even_sub_one_of_odd b hb⟩
  rw [mE8b_gen_eq a b ha hb]
  have hgen : (M12Mod.mx₁ * M12Mod.mx₂ * M12Mod.mtau) ∈ mE8b :=
    Subgroup.subset_closure (k := ({M12Mod.mx₁ ^ 2, (M12Mod.mx₁ * M12Mod.mx₂) ^ 2,
      M12Mod.mx₁ * M12Mod.mx₂ * M12Mod.mtau} : Set M12Mod)) (Or.inr (Or.inr rfl))
  exact mul_mem (mF_le_mE8b hmem) hgen

private theorem sup_zpowers_mE8 {a b : Fin 4} (ha : Even a.val) (hb : Even b.val) :
    mF ⊔ Subgroup.zpowers (⟨a, b, 0, 1⟩ : M12Mod) = mE8 := by
  rw [mE8_eq_sE8]
  refine le_antisymm ?_ ?_
  · refine sup_le mF_le_sE8 ?_
    rw [Subgroup.zpowers_le]
    exact (mem_sE8 _).mpr ⟨rfl, ha, hb⟩
  · intro x hx
    obtain ⟨xa, xb, xi, xj⟩ := x
    rw [mem_sE8] at hx
    obtain ⟨hxi, hxa, hxb⟩ := hx
    by_cases hxj : xj = 0
    · exact Subgroup.mem_sup_left ((mem_mF xa xb xi xj).mpr ⟨hxi, hxj, hxa, hxb⟩)
    · have hmem : (⟨xa, xb, xi, xj⟩ : M12Mod) *
          (⟨a, b, 0, 1⟩ : M12Mod)⁻¹ ∈ mF := by
        rw [mem_mF]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel +revert
      have heq : (⟨xa, xb, xi, xj⟩ : M12Mod) =
          (⟨xa, xb, xi, xj⟩ : M12Mod) * (⟨a, b, 0, 1⟩ : M12Mod)⁻¹ *
            (⟨a, b, 0, 1⟩ : M12Mod) := by group
      rw [heq]
      exact mul_mem (Subgroup.mem_sup_left hmem)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

private theorem sup_zpowers_mE8b {a b : Fin 4} (ha : Odd a.val) (hb : Odd b.val) :
    mF ⊔ Subgroup.zpowers (⟨a, b, 0, 1⟩ : M12Mod) = mE8b := by
  refine le_antisymm ?_ ?_
  · refine sup_le mF_le_mE8b ?_
    rw [Subgroup.zpowers_le]
    exact zpowers_gen_mem_mE8b ha hb
  · rw [mE8b, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (mem_mF_of_even 2 0 (by decide) (by decide))
    · exact Subgroup.mem_sup_left (mem_mF_of_even 2 2 (by decide) (by decide))
    · have hmem : (M12Mod.mx₁ * M12Mod.mx₂ * M12Mod.mtau) *
          (⟨a, b, 0, 1⟩ : M12Mod)⁻¹ ∈ mF := by
        rw [mem_mF]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel +revert
      have heq : (M12Mod.mx₁ * M12Mod.mx₂ * M12Mod.mtau : M12Mod) =
          ((M12Mod.mx₁ * M12Mod.mx₂ * M12Mod.mtau) * (⟨a, b, 0, 1⟩ : M12Mod)⁻¹) *
            (⟨a, b, 0, 1⟩ : M12Mod) := by group
      rw [heq]
      exact mul_mem (Subgroup.mem_sup_left hmem)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

private theorem mem_mA_x1_conj (ua ub : Fin 4) :
    (M12Mod.mx₁ * (⟨ua, ub, 0, 1⟩ : M12Mod) * M12Mod.mx₁⁻¹ *
      (⟨ua, ub, 0, 1⟩ : M12Mod)⁻¹) ∈ mA := by
  rw [mem_mA]
  decide +kernel +revert

private theorem mem_mA_lam_conj (ua ub : Fin 4) :
    (M12Mod.mlam * (⟨ua, ub, 0, 1⟩ : M12Mod) * M12Mod.mlam⁻¹ *
      (⟨ua, ub, 0, 1⟩ : M12Mod)⁻¹) ∈ mA := by
  rw [mem_mA]
  decide +kernel +revert

private theorem mul_inv_gen_mem_mA (ua ub xa xb : Fin 4) (xi xj : Fin 2)
    (hxi : xi = 0) (hxj : xj = 1) :
    (⟨xa, xb, xi, xj⟩ : M12Mod) * (⟨ua, ub, 0, 1⟩ : M12Mod)⁻¹ ∈ mA := by
  rw [mem_mA]
  decide +kernel +revert

private theorem parity_of_conj_mF (ua ub : Fin 4)
    (h1 : M12Mod.mx₁ * (⟨ua, ub, 0, 1⟩ : M12Mod) * M12Mod.mx₁⁻¹ *
      (⟨ua, ub, 0, 1⟩ : M12Mod)⁻¹ ∈ mF)
    (h2 : M12Mod.mlam * (⟨ua, ub, 0, 1⟩ : M12Mod) * M12Mod.mlam⁻¹ *
      (⟨ua, ub, 0, 1⟩ : M12Mod)⁻¹ ∈ mF) :
    (Even ua.val ∧ Even ub.val) ∨ (Odd ua.val ∧ Odd ub.val) := by
  rw [mem_mF] at h1 h2
  decide +kernel +revert

private theorem model_eq_of_normal_elemAbelian_eight (E : Subgroup M12Mod)
    (hE : IsElemAbelian 2 E) (h8 : Nat.card E = 8) (hN : NormalIn E ⊤) :
    E = mE8 ∨ E = mE8b := by
  have h4 : 4 ≤ Nat.card E := by omega
  obtain ⟨hmF_le_E, hE_le_cen⟩ := model_fourGrp_le_of_normal_elemAbelian E hE hN h4
  have hE_mE : E ≤ mE := by rw [← centralizer_mF]; exact hE_le_cen
  have hEA_le_mF : E ⊓ mA ≤ mF := by
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxE, hxmA⟩ := hx
    obtain ⟨a, b, i, j⟩ := x
    have hxA : i = 0 ∧ j = 0 := (mem_mA a b i j).mp hxmA
    obtain ⟨rfl, rfl⟩ := hxA
    rw [mem_mF]
    exact ⟨rfl, rfl, (even_of_sq_one a b (hE.2 _ hxE)).1,
      (even_of_sq_one a b (hE.2 _ hxE)).2⟩
  have hEA : E ⊓ mA = mF := by
    refine le_antisymm hEA_le_mF ?_
    intro x hx
    obtain ⟨a, b, i, j⟩ := x
    have hxmf := (mem_mF a b i j).mp hx
    exact ⟨hmF_le_E hx, (mem_mA a b i j).mpr ⟨hxmf.1, hxmf.2.1⟩⟩
  have hnotA : ¬ E ≤ mA := by
    intro h
    have hEmF : E ≤ mF := fun x hx => hEA ▸ ⟨hx, h hx⟩
    have : Nat.card E ≤ 4 := (Subgroup.card_le_of_le hEmF).trans card_mF_le
    omega
  obtain ⟨u, huE, huA⟩ := Set.not_subset.mp hnotA
  obtain ⟨ua, ub, ui, uj⟩ := u
  have hu_mE : ui = 0 := (mem_mE ua ub ui uj).mp (hE_mE huE)
  have hu_j : uj = 1 := by
    have hne : uj.val ≠ 0 := by
      intro hh
      apply huA
      exact (mem_mA ua ub ui uj).mpr ⟨hu_mE, Fin.ext (by simpa using hh)⟩
    have := uj.isLt
    exact Fin.ext (by omega)
  subst hu_mE
  subst hu_j
  have huE' : (⟨ua, ub, 0, 1⟩ : M12Mod) ∈ E := huE
  have hE_eq : E = mF ⊔ Subgroup.zpowers (⟨ua, ub, 0, 1⟩ : M12Mod) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      by_cases hxA : x ∈ mA
      · exact Subgroup.mem_sup_left (hEA ▸ ⟨hx, hxA⟩)
      · have hx_mE : x ∈ mE := hE_mE hx
        have hquotA : x * (⟨ua, ub, 0, 1⟩ : M12Mod)⁻¹ ∈ mA := by
          obtain ⟨xa, xb, xi, xj⟩ := x
          have hxi : xi = 0 := (mem_mE xa xb xi xj).mp hx_mE
          have hxj : xj = 1 := by
            have hne : xj.val ≠ 0 := by
              intro hh
              apply hxA
              exact (mem_mA xa xb xi xj).mpr ⟨hxi, Fin.ext (by simpa using hh)⟩
            have := xj.isLt
            exact Fin.ext (by omega)
          exact mul_inv_gen_mem_mA ua ub xa xb xi xj hxi hxj
        have hquot : x * (⟨ua, ub, 0, 1⟩ : M12Mod)⁻¹ ∈ E ⊓ mA :=
          ⟨E.mul_mem hx (E.inv_mem huE'), hquotA⟩
        rw [hEA] at hquot
        have heq : x = (x * (⟨ua, ub, 0, 1⟩ : M12Mod)⁻¹) * (⟨ua, ub, 0, 1⟩ : M12Mod) := by
          group
        rw [heq]
        exact mul_mem (Subgroup.mem_sup_left hquot)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    · refine sup_le hmF_le_E ?_
      exact Subgroup.zpowers_le.mpr huE'
  have h1 : M12Mod.mx₁ * (⟨ua, ub, 0, 1⟩ : M12Mod) * M12Mod.mx₁⁻¹ *
      (⟨ua, ub, 0, 1⟩ : M12Mod)⁻¹ ∈ mF := by
    have hconj := hN.2 M12Mod.mx₁ (Subgroup.mem_top _) _ huE'
    rw [← hEA]
    exact ⟨E.mul_mem hconj (E.inv_mem huE'), mem_mA_x1_conj ua ub⟩
  have h2 : M12Mod.mlam * (⟨ua, ub, 0, 1⟩ : M12Mod) * M12Mod.mlam⁻¹ *
      (⟨ua, ub, 0, 1⟩ : M12Mod)⁻¹ ∈ mF := by
    have hconj := hN.2 M12Mod.mlam (Subgroup.mem_top _) _ huE'
    rw [← hEA]
    exact ⟨E.mul_mem hconj (E.inv_mem huE'), mem_mA_lam_conj ua ub⟩
  rcases parity_of_conj_mF ua ub h1 h2 with hpar | hpar
  · left
    rw [hE_eq, sup_zpowers_mE8 hpar.1 hpar.2]
  · right
    rw [hE_eq, sup_zpowers_mE8b hpar.1 hpar.2]

private theorem baseGrp_le_m12Grp : baseGrp x₁ x₂ ≤ m12Grp x₁ x₂ lam tau := by
  unfold baseGrp m12Grp
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  tauto

private theorem fourGrp_le_m12Grp : fourGrp x₁ x₂ ≤ m12Grp x₁ x₂ lam tau := by
  unfold fourGrp m12Grp
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx
  · rw [hx]
    exact pow_mem (Subgroup.subset_closure (k := ({x₁, x₂, lam, tau} : Set G)) (by simp)) 2
  · rw [hx]
    exact pow_mem
      (mul_mem (Subgroup.subset_closure (k := ({x₁, x₂, lam, tau} : Set G)) (by simp))
        (Subgroup.subset_closure (k := ({x₁, x₂, lam, tau} : Set G)) (by simp))) 2

private theorem map_mA_eq (φ : M12Mod →* G) (h1 : φ M12Mod.mx₁ = x₁)
    (h2 : φ M12Mod.mx₂ = x₂) : mA.map φ = baseGrp x₁ x₂ := by
  unfold mA baseGrp
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, hzy⟩
    rw [← hzy]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    rcases hz with hz | hz
    · rw [hz]; exact Or.inl h1
    · rw [hz]; exact Or.inr h2
  · intro hy
    rcases hy with hy | hy
    · rw [hy]; exact ⟨M12Mod.mx₁, Or.inl rfl, h1⟩
    · rw [hy]; exact ⟨M12Mod.mx₂, Or.inr rfl, h2⟩

private theorem map_mF_eq (φ : M12Mod →* G) (h1 : φ M12Mod.mx₁ = x₁)
    (h2 : φ M12Mod.mx₂ = x₂) : mF.map φ = fourGrp x₁ x₂ := by
  unfold mF fourGrp
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, hzy⟩
    rw [← hzy]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    rcases hz with hz | hz
    · rw [hz]; left; rw [map_pow, h1]
    · rw [hz]; right; rw [map_pow, map_mul, h1, h2]
  · intro hy
    rcases hy with hy | hy
    · rw [hy]
      exact ⟨M12Mod.mx₁ ^ 2, Or.inl rfl, by rw [map_pow, h1]⟩
    · rw [hy]
      exact ⟨(M12Mod.mx₁ * M12Mod.mx₂) ^ 2, Or.inr rfl, by rw [map_pow, map_mul, h1, h2]⟩

private theorem mE_eq_mA_sup : mE = mA ⊔ Subgroup.zpowers M12Mod.mtau := by
  unfold mE mA baseGrp
  rw [Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
  congr 1
  ext z
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem map_mE_embed (φ : M12Mod →* G) (h1 : φ M12Mod.mx₁ = x₁)
    (h2 : φ M12Mod.mx₂ = x₂) (h4 : φ M12Mod.mtau = tau) :
    mE.map φ = baseGrp x₁ x₂ ⊔ Subgroup.zpowers tau := by
  rw [mE_eq_mA_sup, Subgroup.map_sup, map_mA_eq φ h1 h2, MonoidHom.map_zpowers, h4]

private theorem map_mE8_eq (φ : M12Mod →* G) (h1 : φ M12Mod.mx₁ = x₁)
    (h2 : φ M12Mod.mx₂ = x₂) (h4 : φ M12Mod.mtau = tau) :
    mE8.map φ = Subgroup.closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, tau} : Set G) := by
  unfold mE8
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, hzy⟩
    rw [← hzy]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    rcases hz with hz | hz | hz
    · rw [hz]; left; rw [map_pow, h1]
    · rw [hz]; right; left; rw [map_pow, map_mul, h1, h2]
    · rw [hz]; right; right; exact h4
  · intro hy
    rcases hy with hy | hy | hy
    · rw [hy]
      exact ⟨M12Mod.mx₁ ^ 2, Or.inl rfl, by rw [map_pow, h1]⟩
    · rw [hy]
      exact ⟨(M12Mod.mx₁ * M12Mod.mx₂) ^ 2, Or.inr (Or.inl rfl),
        by rw [map_pow, map_mul, h1, h2]⟩
    · rw [hy]
      exact ⟨M12Mod.mtau, Or.inr (Or.inr rfl), h4⟩

private theorem map_mE8b_eq (φ : M12Mod →* G) (h1 : φ M12Mod.mx₁ = x₁)
    (h2 : φ M12Mod.mx₂ = x₂) (h4 : φ M12Mod.mtau = tau) :
    mE8b.map φ = Subgroup.closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, x₁ * x₂ * tau} : Set G) := by
  unfold mE8b
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, hzy⟩
    rw [← hzy]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    rcases hz with hz | hz | hz
    · rw [hz]; left; rw [map_pow, h1]
    · rw [hz]; right; left; rw [map_pow, map_mul, h1, h2]
    · rw [hz]; right; right; rw [map_mul, map_mul, h1, h2, h4]
  · intro hy
    rcases hy with hy | hy | hy
    · rw [hy]
      exact ⟨M12Mod.mx₁ ^ 2, Or.inl rfl, by rw [map_pow, h1]⟩
    · rw [hy]
      exact ⟨(M12Mod.mx₁ * M12Mod.mx₂) ^ 2, Or.inr (Or.inl rfl),
        by rw [map_pow, map_mul, h1, h2]⟩
    · rw [hy]
      exact ⟨M12Mod.mx₁ * M12Mod.mx₂ * M12Mod.mtau, Or.inr (Or.inr rfl),
        by rw [map_mul, map_mul, h1, h2, h4]⟩

private theorem eq_of_comap_eq {φ : M12Mod →* G} {A B : Subgroup G}
    (hA : A ≤ φ.range) (hB : B ≤ φ.range) (h : A.comap φ = B.comap φ) : A = B := by
  rw [← Subgroup.map_comap_eq_self hA, h, Subgroup.map_comap_eq_self hB]

private theorem map_centralizer_le (φ : M12Mod →* G) (h1 : φ M12Mod.mx₁ = x₁)
    (h2 : φ M12Mod.mx₂ = x₂) :
    (Subgroup.centralizer (mF : Set M12Mod)).map φ ≤
      Subgroup.centralizer (fourGrp x₁ x₂ : Set G) := by
  rw [← map_mF_eq φ h1 h2]
  exact Subgroup.map_centralizer_le_centralizer_image (mF : Set M12Mod) φ

private theorem comap_centralizer {φ : M12Mod →* G} (hinj : Function.Injective φ)
    (T : Subgroup G) (hT : T ≤ φ.range) :
    (Subgroup.centralizer (T : Set G)).comap φ =
      Subgroup.centralizer ((T.comap φ : Subgroup M12Mod) : Set M12Mod) := by
  ext g
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h t ht
    apply hinj
    rw [map_mul, map_mul]
    exact h (φ t) ht
  · intro h y hy
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp (hT hy)
    rw [← map_mul, ← map_mul]
    exact congrArg φ (h t hy)

private theorem isElemAbelian_comap {φ : M12Mod →* G} (hinj : Function.Injective φ)
    {E : Subgroup G} (hE : IsElemAbelian 2 E) : IsElemAbelian 2 (E.comap φ) := by
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro a b
    apply Subtype.ext
    apply hinj
    show φ (a.1 * b.1) = φ (b.1 * a.1)
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨φ a.1, a.2⟩ ⟨φ b.1, b.2⟩)
  · intro x hx
    apply hinj
    show φ (x ^ 2) = φ 1
    rw [map_pow, hE.2 (φ x) hx, map_one]

private theorem normalIn_comap {φ : M12Mod →* G} (hrange : φ.range = m12Grp x₁ x₂ lam tau)
    {E : Subgroup G} (hN : NormalIn E (m12Grp x₁ x₂ lam tau)) :
    NormalIn (E.comap φ) ⊤ := by
  refine ⟨le_top, ?_⟩
  intro g _ k hk
  rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact hN.2 (φ g) (by rw [← hrange]; exact ⟨g, rfl⟩) (φ k) hk

private theorem card_comap_eq {φ : M12Mod →* G} (hinj : Function.Injective φ)
    {E : Subgroup G} (hE : E ≤ φ.range) : Nat.card (E.comap φ) = Nat.card E := by
  rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq_self hE]

private theorem comap_fourGrp {φ : M12Mod →* G} (hinj : Function.Injective φ)
    (h1 : φ M12Mod.mx₁ = x₁) (h2 : φ M12Mod.mx₂ = x₂) :
    (fourGrp x₁ x₂).comap φ = mF := by
  rw [← map_mF_eq φ h1 h2, Subgroup.comap_map_eq_self_of_injective hinj]

theorem M12Rel.centralizer_fourGrp (h : M12Rel x₁ x₂ lam tau) :
    m12Grp x₁ x₂ lam tau ⊓ centralizer (fourGrp x₁ x₂ : Set G) =
      baseGrp x₁ x₂ ⊔ zpowers tau := by
  obtain ⟨φ, hinj, hrange, h1, h2, h3, h4⟩ := h.exists_embedding
  have hfour : fourGrp x₁ x₂ ≤ φ.range := by rw [hrange]; exact fourGrp_le_m12Grp
  have hA : m12Grp x₁ x₂ lam tau ⊓ centralizer (fourGrp x₁ x₂ : Set G) ≤ φ.range := by
    rw [hrange]; exact inf_le_left
  have hB : baseGrp x₁ x₂ ⊔ Subgroup.zpowers tau ≤ φ.range := by
    rw [hrange]
    exact sup_le baseGrp_le_m12Grp (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
  apply eq_of_comap_eq hA hB
  rw [Subgroup.comap_inf]
  rw [show m12Grp x₁ x₂ lam tau = φ.range from hrange.symm, MonoidHom.comap_range_self,
    top_inf_eq]
  rw [comap_centralizer hinj (fourGrp x₁ x₂) hfour, comap_fourGrp hinj h1 h2, centralizer_mF]
  rw [← map_mE_embed φ h1 h2 h4, Subgroup.comap_map_eq_self_of_injective hinj]

theorem M12Rel.fourGrp_le_of_normal_elemAbelian (h : M12Rel x₁ x₂ lam tau) {E : Subgroup G}
    (hE : IsElemAbelian 2 E) (hN : NormalIn E (m12Grp x₁ x₂ lam tau)) (h4 : 4 ≤ Nat.card E) :
    fourGrp x₁ x₂ ≤ E ∧ E ≤ m12Grp x₁ x₂ lam tau ⊓ centralizer (fourGrp x₁ x₂ : Set G) := by
  obtain ⟨φ, hinj, hrange, h1, h2, h3, htau⟩ := h.exists_embedding
  have hE_range : E ≤ φ.range := by rw [hrange]; exact hN.1
  have h4' : 4 ≤ Nat.card (E.comap φ) := by
    rw [card_comap_eq hinj hE_range]; exact h4
  obtain ⟨hmF_le, hE_le_cen⟩ := model_fourGrp_le_of_normal_elemAbelian (E.comap φ)
    (isElemAbelian_comap hinj hE) (normalIn_comap hrange hN) h4'
  constructor
  · have hle := Subgroup.map_mono (f := φ) hmF_le
    rw [map_mF_eq φ h1 h2, Subgroup.map_comap_eq_self hE_range] at hle
    exact hle
  · have hle := Subgroup.map_mono (f := φ) hE_le_cen
    rw [Subgroup.map_comap_eq_self hE_range] at hle
    exact le_inf hN.1 (hle.trans (map_centralizer_le φ h1 h2))

theorem M12Rel.card_le_eight_of_elemAbelian (h : M12Rel x₁ x₂ lam tau) {E : Subgroup G}
    (hEX : E ≤ m12Grp x₁ x₂ lam tau) (hE : IsElemAbelian 2 E) : Nat.card E ≤ 8 := by
  obtain ⟨φ, hinj, hrange, h1, h2, h3, h4⟩ := h.exists_embedding
  have hEX_range : E ≤ φ.range := by rw [hrange]; exact hEX
  have h := model_card_le_eight (E.comap φ) (isElemAbelian_comap hinj hE)
  rw [card_comap_eq hinj hEX_range] at h
  exact h

theorem M12Rel.centralizer_eq_of_elemAbelian_eight (h : M12Rel x₁ x₂ lam tau) {E : Subgroup G}
    (hEX : E ≤ m12Grp x₁ x₂ lam tau) (hE : IsElemAbelian 2 E) (hcard : Nat.card E = 8) :
    m12Grp x₁ x₂ lam tau ⊓ centralizer (E : Set G) = E := by
  obtain ⟨φ, hinj, hrange, h1, h2, h3, h4⟩ := h.exists_embedding
  have hE_range : E ≤ φ.range := by rw [hrange]; exact hEX
  have hA : m12Grp x₁ x₂ lam tau ⊓ centralizer (E : Set G) ≤ φ.range := by
    rw [hrange]; exact inf_le_left
  apply eq_of_comap_eq hA hE_range
  rw [Subgroup.comap_inf]
  rw [show m12Grp x₁ x₂ lam tau = φ.range from hrange.symm, MonoidHom.comap_range_self,
    top_inf_eq]
  rw [comap_centralizer hinj E hE_range]
  rw [model_centralizer_eq_eight (E.comap φ) (isElemAbelian_comap hinj hE)
    (by rw [card_comap_eq hinj hE_range]; exact hcard)]

theorem M12Rel.eq_of_normal_elemAbelian_eight (h : M12Rel x₁ x₂ lam tau) {E : Subgroup G}
    (hEX : E ≤ m12Grp x₁ x₂ lam tau) (hE : IsElemAbelian 2 E) (hcard : Nat.card E = 8)
    (hN : NormalIn E (m12Grp x₁ x₂ lam tau)) :
    E = closure {x₁ ^ 2, (x₁ * x₂) ^ 2, tau} ∨
        E = closure {x₁ ^ 2, (x₁ * x₂) ^ 2, x₁ * x₂ * tau} := by
  obtain ⟨φ, hinj, hrange, h1, h2, h3, h4⟩ := h.exists_embedding
  have hE_range : E ≤ φ.range := by rw [hrange]; exact hEX
  have hcard' : Nat.card (E.comap φ) = 8 := by
    rw [card_comap_eq hinj hE_range]; exact hcard
  rcases model_eq_of_normal_elemAbelian_eight (E.comap φ) (isElemAbelian_comap hinj hE)
    hcard' (normalIn_comap hrange hN) with hmod | hmod
  · left
    rw [← Subgroup.map_comap_eq_self hE_range, hmod, map_mE8_eq φ h1 h2 h4]
  · right
    rw [← Subgroup.map_comap_eq_self hE_range, hmod, map_mE8b_eq φ h1 h2 h4]

end CFSG.OddStandard.SmallF3.HarrisU33
