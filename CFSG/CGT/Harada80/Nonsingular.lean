module

public import CFSG.CGT.Harada80.NonsingularLin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Harada80.Setting

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.RankThree.PartTwo QuadraticMap

variable {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ} {S : Setting G M J m}

theorem exists_singular_pair_perp_blockU (hZ : blockZ J = ⊥) {b : ↥(blockU J)}
    (hb : quadQ m (S.vec b) = 1) :
    ∃ u₁ u₂ : ↥(blockU J), u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₁ * u₂ ≠ 1 ∧
      quadQ m (S.vec u₁) = 0 ∧ quadQ m (S.vec u₂) = 0 ∧ quadQ m (S.vec (u₁ * u₂)) = 0 ∧
      polar (quadQ m) (S.vec u₁) (S.vec b) = 0 ∧ polar (quadQ m) (S.vec u₂) (S.vec b) = 0 := by
  have h6 : 6 ≤ Module.finrank (ZMod 2) (Vec m) := by
    rw [CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.finrank_minus]
    rcases S.m_eq with h | h <;> omega
  obtain ⟨v₁, v₂, hv₁, hv₂, hv₁₂, hq₁, hq₂, hp, hpb₁, hpb₂⟩ :=
    exists_singular_pair_perp (Q := quadQ m) (nondegenerate_quadQ m) h6 hb
  obtain ⟨u₁, rfl⟩ := S.vec_surjective v₁
  obtain ⟨u₂, rfl⟩ := S.vec_surjective v₂
  have hu₁ : u₁ ≠ 1 := fun h => hv₁ ((S.vec_eq_zero_iff hZ).mpr h)
  have hu₂ : u₂ ≠ 1 := fun h => hv₂ ((S.vec_eq_zero_iff hZ).mpr h)
  have hu₁₂ : u₁ * u₂ ≠ 1 := by
    intro h
    have hv : S.vec u₁ + S.vec u₂ = 0 := by rw [← S.vec_mul, h, S.vec_one]
    have hEq : S.vec u₁ = S.vec u₂ := by
      have h' : S.vec u₁ = -S.vec u₂ := eq_neg_of_add_eq_zero_left hv
      rwa [ZModModule.neg_eq_self] at h'
    exact hv₁₂ hEq
  refine ⟨u₁, u₂, hu₁, hu₂, hu₁₂, hq₁, hq₂, ?_, hpb₁, hpb₂⟩
  rw [S.vec_mul, QuadraticMap.map_add (quadQ m), hq₁, hq₂, hp]
  ring

private theorem map_conj_eq_of_mem_sup_of_perp (hE : BlockCase J m) {b : ↥(blockU J)}
    (hb : quadQ m (S.vec b) = 1) {w : G} (hw : w ∈ blockW J)
    (hperp : ∀ g : G, (∀ a : ↥(blockU J), polar (quadQ m) (S.vec a) (S.vec b) = 0 →
      ∀ w' ∈ blockW J, g⁻¹ * ((a : G) * w') * g ∈ pCoreOf 2 M) → g ∈ M)
    (y : G)
    (hle : (pCoreOf 2 M).map (MulAut.conj y).toMonoidHom ≤
      (pCoreOf 2 (Subgroup.centralizer ({(b : G) * w} : Set G)) ⊔ pCoreOf 2 M) ⊓ M) :
    (pCoreOf 2 M).map (MulAut.conj y).toMonoidHom = pCoreOf 2 M := by
  classical
  let H : Subgroup G := Subgroup.centralizer ({(b : G) * w} : Set G)
  let R : Subgroup G := pCoreOf 2 H
  let AW : Subgroup G := pCoreOf 2 M
  by_contra hne
  have hKleM : ((R ⊔ AW) ⊓ M) ≤ M := inf_le_right
  have hT : IsPGroup 2 ↥((R ⊔ AW) ⊓ M) := by
    simpa [H, R, AW] using
      isPGroup_inf_sup_pCoreOf_centralizer (S := S) hE (u := b) hw
  have hTb : ∀ t ∈ (R ⊔ AW) ⊓ M, t * (b : G) * t⁻¹ = b := by
    intro t ht
    exact conj_eq_of_mem_inf_sup_pCoreOf_centralizer (S := S) hE hw
      (by simpa [H, R, AW] using ht)
  have hTn : ∀ ℓ ∈ J, ℓ * (b : G) * ℓ⁻¹ = b →
      ∀ t ∈ (R ⊔ AW) ⊓ M, ℓ * t * ℓ⁻¹ ∈ (R ⊔ AW) ⊓ M := by
    intro ℓ hℓJ hℓb t ht
    exact conj_mem_inf_sup_pCoreOf_centralizer_of_centralizes (S := S) hE hw hℓJ hℓb
      (by simpa [H, R, AW] using ht)
  have hBab : ∀ p ∈ AW.map (MulAut.conj y).toMonoidHom,
      ∀ q ∈ AW.map (MulAut.conj y).toMonoidHom, p * q = q * p := by
    intro p hp q hq
    obtain ⟨p₀, hp₀, rfl⟩ := Subgroup.mem_map.mp hp
    obtain ⟨q₀, hq₀, rfl⟩ := Subgroup.mem_map.mp hq
    rw [← map_mul, ← map_mul, pCoreOf_comm (S := S) hE hp₀ hq₀]
  have hcard : Nat.card (pCoreOf 2 M) ≤
      Nat.card ↥(AW.map (MulAut.conj y).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (K := AW)
      (f := (MulAut.conj y).toMonoidHom) (MulAut.conj y).injective]
  have hmem : ∀ a : ↥(blockU J), polar (quadQ m) (S.vec a) (S.vec b) = 0 →
      ∀ w' ∈ blockW J, (a : G) * w' ∈ AW.map (MulAut.conj y).toMonoidHom :=
    fun a ha w' hw' =>
      mul_mem_of_nonsingular (S := S) hE hb hKleM hT hTb hTn
        (by simpa [H, R, AW] using hle) hBab hcard hne ha hw'
  have hyM : y ∈ M := by
    refine hperp y fun a ha w' hw' => ?_
    obtain ⟨v, hv, hveq⟩ := Subgroup.mem_map.mp (hmem a ha w' hw')
    have hc : y * v * y⁻¹ = (a : G) * w' := by
      simpa [MulAut.conj_apply] using hveq
    have hveq' : y⁻¹ * ((a : G) * w') * y = v := by rw [← hc]; group
    rwa [hveq']
  have hyN : y ∈ Subgroup.normalizer (AW : Set G) := by
    rw [show AW = pCoreOf 2 M from rfl,
      CFSG.RankThree.PartTwo.Late.normalizer_pCoreOf_of_isMaximalTwoLocal S.maxLocal]
    exact hyM
  exact hne (Subgroup.mem_normalizer_iff_map_conj_eq.mp hyN)

theorem pCoreOf_centralizer_le_of_perp (hE : BlockCase J m) {b : ↥(blockU J)}
    (hb : quadQ m (S.vec b) = 1) {w : G} (hw : w ∈ blockW J)
    (hperp : ∀ g : G, (∀ a : ↥(blockU J), polar (quadQ m) (S.vec a) (S.vec b) = 0 →
      ∀ w' ∈ blockW J, g⁻¹ * ((a : G) * w') * g ∈ pCoreOf 2 M) → g ∈ M) :
    pCoreOf 2 (Subgroup.centralizer ({(b : G) * w} : Set G)) ≤ M := by
  classical
  let H : Subgroup G := Subgroup.centralizer ({(b : G) * w} : Set G)
  let R : Subgroup G := pCoreOf 2 H
  let AW : Subgroup G := pCoreOf 2 M
  have hAWleH : AW ≤ H := pCoreOf_le_centralizer_mul S hE hw
  have hHleNR : H ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.le_normalizer (H := H)).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H)
  have hJR : AW ≤ Subgroup.normalizer (R : Set G) := hAWleH.trans hHleNR
  have hJM : AW ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hNJ : Subgroup.normalizer (AW : Set G) ≤ M := by
    rw [show AW = pCoreOf 2 M from rfl,
      CFSG.RankThree.PartTwo.Late.normalizer_pCoreOf_of_isMaximalTwoLocal S.maxLocal]
  refine CFSG.CGT.Hall82.le_of_forall_map_conj_eq (p := 2) (M := M) (J := AW) (R := R)
    hJM hNJ ?_ ?_ hJR ?_
  · exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  · exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  · intro y _ hle
    exact map_conj_eq_of_mem_sup_of_perp (S := S) hE hb hw hperp y
      (by simpa [H, R, AW] using hle)

theorem lin_eq_one_or_eq_reflect_of_mem (hE : BlockCase J m) (hZ : blockZ J = ⊥)
    {b : ↥(blockU J)} (hb : quadQ m (S.vec b) = 1) {w : G} (hw : w ∈ blockW J)
    (hR : pCoreOf 2 (Subgroup.centralizer ({(b : G) * w} : Set G)) ≤ M) {x : G}
    (hx : x ∈ pCoreOf 2 (Subgroup.centralizer ({(b : G) * w} : Set G))) :
    S.lin hZ ⟨x, hR hx⟩ = 1 ∨
      S.lin hZ ⟨x, hR hx⟩ = CFSG.ClassicalGroups.Orthogonal.reflect (quadQ m) (S.vec b) := by
  let H : Subgroup G := Subgroup.centralizer ({(b : G) * w} : Set G)
  have hTb : ∀ t ∈ pCoreOf 2 H, t * (b : G) * t⁻¹ = b := by
    intro t ht
    exact conj_eq_of_mem_centralizer_mul (S := S) hE hw
      (hR (by simpa [H] using ht)) (by simpa [H] using CFSG.LieType.BorelTits.pCoreOf_le 2 H ht)
  have hTn : ∀ ℓ ∈ J, ℓ * (b : G) * ℓ⁻¹ = b →
      ∀ t ∈ pCoreOf 2 H, ℓ * t * ℓ⁻¹ ∈ pCoreOf 2 H := by
    intro ℓ hℓJ hℓb t ht
    exact conj_mem_pCoreOf_centralizer_of_centralizes hw hℓJ hℓb ht
  exact lin_eq_one_or_eq_reflect (S := S) hZ hb (by simpa [H] using hR)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hTb hTn (by simpa [H] using hx)

theorem mem_pCoreOf_centralizer_of_perp (hE : BlockCase J m) {b : ↥(blockU J)}
    (hb : quadQ m (S.vec b) = 1) {w : G} (hw : w ∈ blockW J)
    (hR : pCoreOf 2 (Subgroup.centralizer ({(b : G) * w} : Set G)) ≤ M)
    {a : ↥(blockU J)} (ha : polar (quadQ m) (S.vec a) (S.vec b) = 0) :
    (a : G) ∈ pCoreOf 2 (Subgroup.centralizer ({(b : G) * w} : Set G)) := by
  have hZ : blockZ J = ⊥ := S.blockZ_eq_bot hE.h1
  have hAH : (a : G) ∈ Subgroup.centralizer ({(b : G) * w} : Set G) :=
    pCoreOf_le_centralizer_mul S hE hw (blockU_le_pCoreOf S a.2)
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, S.vec_one, map_zero] at hb
    exact zero_ne_one hb
  have htAW : ((b : G) * w) ∈ pCoreOf 2 M := by
    rw [pCoreOf_eq (S := S) hE]
    exact Subgroup.mul_mem_sup b.2 hw
  have ht1 : ((b : G) * w) ≠ 1 :=
    fun h1 => mul_notMem_blockW S hZ hb1 hw (h1 ▸ (blockW J).one_mem)
  refine le_pCoreOf_of_centralizes (S := S) htAW ht1 hAH ?_
  intro y hy
  have hya : y * (a : G) * y⁻¹ = a := by
    have hlin := lin_eq_one_or_eq_reflect_of_mem (S := S) hE hZ hb hw hR hy
    have hfix : S.lin hZ ⟨y, hR hy⟩ (S.vec a) = S.vec a := by
      rcases hlin with h1 | hr
      · rw [h1]; simp
      · rw [hr]; exact (reflect_apply_eq_self_iff hb).mpr ha
    exact (S.lin_vec_eq_iff hZ ⟨y, hR hy⟩ a).mp hfix
  have hycomm : y * (a : G) = (a : G) * y := by
    calc y * (a : G) = (y * (a : G) * y⁻¹) * y := by group
      _ = (a : G) * y := by rw [hya]
  exact hycomm.symm

theorem mem_pCoreOf_or_of_mem (hE : BlockCase J m) {b : ↥(blockU J)}
    (hb : quadQ m (S.vec b) = 1) {w : G} (hw : w ∈ blockW J)
    (hR : pCoreOf 2 (Subgroup.centralizer ({(b : G) * w} : Set G)) ≤ M) {x₁ x₂ : G}
    (h1 : x₁ ∈ pCoreOf 2 (Subgroup.centralizer ({(b : G) * w} : Set G)))
    (h2 : x₂ ∈ pCoreOf 2 (Subgroup.centralizer ({(b : G) * w} : Set G))) :
    x₁ ∈ pCoreOf 2 M ∨ x₂ ∈ pCoreOf 2 M ∨ x₁ * x₂ ∈ pCoreOf 2 M := by
  let H : Subgroup G := Subgroup.centralizer ({(b : G) * w} : Set G)
  let R : Subgroup G := pCoreOf 2 H
  have hZ : blockZ J = ⊥ := S.blockZ_eq_bot hE.h1
  have hT : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hx₁ := lin_eq_one_or_eq_reflect_of_mem (S := S) hE hZ hb hw hR h1
  rcases hx₁ with h1' | h1'
  · left
    exact mem_pCoreOf_of_lin_eq_one (S := S) hE hZ hR hT h1 (by simpa [H, R] using h1')
  have hx₂ := lin_eq_one_or_eq_reflect_of_mem (S := S) hE hZ hb hw hR h2
  rcases hx₂ with h2' | h2'
  · right; left
    exact mem_pCoreOf_of_lin_eq_one (S := S) hE hZ hR hT h2 (by simpa [H, R] using h2')
  · right; right
    have h12 : S.lin hZ ⟨x₁ * x₂, hR (R.mul_mem h1 h2)⟩ = 1 := by
      rw [show (⟨x₁ * x₂, hR (R.mul_mem h1 h2)⟩ : ↥M) =
          ⟨x₁, hR h1⟩ * ⟨x₂, hR h2⟩ from rfl, map_mul, h1', h2',
        CFSG.ClassicalGroups.Orthogonal.reflect_mul_self]
    exact mem_pCoreOf_of_lin_eq_one (S := S) hE hZ hR hT (R.mul_mem h1 h2) h12

end CFSG.CGT.Harada80.Setting
