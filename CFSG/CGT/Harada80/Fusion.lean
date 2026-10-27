module

public import CFSG.CGT.Harada80.Nonsingular
public import CFSG.CGT.Harada80.SingularCent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Harada80.Setting

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.RankThree.PartTwo QuadraticMap

variable {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ} {S : Setting G M J m}

private theorem exists_subtype_mul_of_mem_pCoreOf (S : Setting G M J m) (hE : BlockCase J m)
    {x : G} (hx : x ∈ pCoreOf 2 M) :
    ∃ a : ↥(blockU J), ∃ w ∈ blockW J, x = (a : G) * w := by
  obtain ⟨a, ha, w, hw, hxw⟩ := exists_mul_of_mem_pCoreOf (S := S) hE hx
  exact ⟨⟨a, ha⟩, w, hw, hxw⟩

private theorem mul_eq_mul_of_mem (S : Setting G M J m) {a a' : ↥(blockU J)} {w w' : G}
    (hw : w ∈ blockW J) (hw' : w' ∈ blockW J) :
    ((a : G) * w) * ((a' : G) * w') = ((a * a' : ↥(blockU J)) : G) * (w * w') := by
  have hcomm : w * (a' : G) = (a' : G) * w := (commute_blockU_blockW S a'.2 hw).symm
  rw [Subgroup.coe_mul]
  calc (a : G) * w * ((a' : G) * w') = (a : G) * (w * (a' : G)) * w' := by group
    _ = (a : G) * ((a' : G) * w) * w' := by rw [hcomm]
    _ = ((a : G) * (a' : G)) * (w * w') := by group

private theorem quadQ_vec_eq_one_of_conj_mem_of_mem_blockW (hE : EvenCase J m) {z : G}
    (hz : z ∈ blockW J) (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1)
    {a : ↥(blockU J)} {w' : G} (hw' : w' ∈ blockW J) {g : G}
    (hg : g⁻¹ * z * g = (a : G) * w') (hgM : g ∉ M) :
    quadQ m (S.vec a) = 1 := by
  rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one (quadQ m (S.vec a)) with h0 | h1
  · by_cases ha1 : a = 1
    · exfalso
      have hCz : z ∈ Subgroup.centralizer (J : Set G) :=
        CFSG.LieType.BorelTits.pCoreOf_le 2 _ hz
      have hgz : g⁻¹ * z * g ∈ Subgroup.centralizer (J : Set G) := by
        rw [hg, ha1]
        simpa using CFSG.LieType.BorelTits.pCoreOf_le 2 _ hw'
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hzord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
      have hginvM : g⁻¹ ∈ M :=
        CFSG.CGT.Hall82.mem_of_common_involution_of_isMaximalTwoLocal
          (M := M) (X := J) S.maxLocal S.uniq hCz hzord (by simpa using hgz)
      exact hgM (by simpa using M.inv_mem hginvM)
    · exact (conj_ne_of_singular (S := S) hE.toBlockCase ha1 h0 hw' hz hz1 g⁻¹
        (by simpa using hg)).elim
  · exact h1

private theorem quadQ_vec_eq_one_of_conj_mem_of_singular (hE : EvenCase J m)
    {u : ↥(blockU J)} (hu1 : u ≠ 1) (hu : quadQ m (S.vec u) = 0) {w : G}
    (hw : w ∈ blockW J) {a : ↥(blockU J)} {w' : G} (hw' : w' ∈ blockW J) {g : G}
    (hg : g⁻¹ * ((u : G) * w) * g = (a : G) * w') (hgM : g ∉ M) :
    quadQ m (S.vec a) = 1 := by
  have hZ : blockZ J = ⊥ := S.blockZ_eq_bot hE.toBlockCase.h1
  rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one (quadQ m (S.vec a)) with h0 | h1
  · by_cases ha1 : a = 1
    · exfalso
      have hw'1 : w' ≠ 1 := by
        intro h
        have heq1 : g⁻¹ * ((u : G) * w) * g = 1 := by
          rw [hg, ha1, h]
          simp
        have h2 : (u : G) * w = 1 := by
          calc (u : G) * w = g * (g⁻¹ * ((u : G) * w) * g) * g⁻¹ := by group
            _ = g * 1 * g⁻¹ := by rw [heq1]
            _ = 1 := by group
        exact mul_notMem_blockW S hZ hu1 hw (h2 ▸ (blockW J).one_mem)
      have hconj : g * w' * g⁻¹ = (u : G) * w := by
        calc g * w' * g⁻¹ = g * ((a : G) * w') * g⁻¹ := by rw [ha1]; simp
          _ = g * (g⁻¹ * ((u : G) * w) * g) * g⁻¹ := by rw [← hg]
          _ = (u : G) * w := by group
      exact (conj_ne_of_singular (S := S) hE.toBlockCase hu1 hu hw hw' hw'1 g hconj).elim
    · have hg' : g ∈ M := by
        simpa using M.inv_mem (mem_of_conj_eq_of_singular (S := S) hE hu1 ha1 hu h0 hw hw'
          (g := g⁻¹) (by simpa using hg))
      exact (hgM hg').elim
  · exact h1

private theorem quadQ_vec_eq_one_of_conj_mul (hE : EvenCase J m)
    {u u' : ↥(blockU J)} {w w' : G}
    (hu1 : u * u' ≠ 1) (hu : quadQ m (S.vec (u * u')) = 0)
    (hw : w ∈ blockW J) (hw' : w' ∈ blockW J)
    {a a' : ↥(blockU J)} {v v' : G} (hv : v ∈ blockW J) (hv' : v' ∈ blockW J)
    {g : G} (heq : g⁻¹ * ((u : G) * w) * g = (a : G) * v)
    (heq' : g⁻¹ * ((u' : G) * w') * g = (a' : G) * v') (hgM : g ∉ M) :
    quadQ m (S.vec (a * a')) = 1 := by
  have hprod : g⁻¹ * (((u * u' : ↥(blockU J)) : G) * (w * w')) * g =
      ((a * a' : ↥(blockU J)) : G) * (v * v') := by
    calc g⁻¹ * (((u * u' : ↥(blockU J)) : G) * (w * w')) * g
        = g⁻¹ * (((u : G) * w) * ((u' : G) * w')) * g := by
          rw [← mul_eq_mul_of_mem S hw hw']
      _ = (g⁻¹ * ((u : G) * w) * g) * (g⁻¹ * ((u' : G) * w') * g) := by group
      _ = ((a : G) * v) * ((a' : G) * v') := by rw [heq, heq']
      _ = ((a * a' : ↥(blockU J)) : G) * (v * v') := mul_eq_mul_of_mem S hv hv'
  exact quadQ_vec_eq_one_of_conj_mem_of_singular (S := S) hE hu1 hu
    ((blockW J).mul_mem hw hw') ((blockW J).mul_mem hv hv') hprod hgM

private theorem quadQ_add_add_add_ne_one {a₁ a₂ a₃ : ↥(blockU J)}
    (h1 : quadQ m (S.vec a₁) = 1) (h2 : quadQ m (S.vec a₂) = 1)
    (h3 : quadQ m (S.vec a₃) = 1)
    (h12 : quadQ m (S.vec (a₁ * a₂)) = 1) (h13 : quadQ m (S.vec (a₁ * a₃)) = 1)
    (h23 : quadQ m (S.vec (a₂ * a₃)) = 1) (h123 : quadQ m (S.vec (a₁ * a₂ * a₃)) = 1) :
    False := by
  have hvec12 : S.vec a₁ + S.vec a₂ = S.vec (a₁ * a₂) := (S.vec_mul a₁ a₂).symm
  have hvec13 : S.vec a₁ + S.vec a₃ = S.vec (a₁ * a₃) := (S.vec_mul a₁ a₃).symm
  have hvec23 : S.vec a₂ + S.vec a₃ = S.vec (a₂ * a₃) := (S.vec_mul a₂ a₃).symm
  have hvec123 : S.vec a₁ + S.vec a₂ + S.vec a₃ = S.vec (a₁ * a₂ * a₃) := by
    rw [hvec12, ← S.vec_mul]
  have hmain := QuadraticMap.map_add_add_add_map (quadQ m) (S.vec a₁) (S.vec a₂) (S.vec a₃)
  rw [hvec123, h1, h2, h3, h123, hvec12, h12, hvec23, h23,
    add_comm (S.vec a₃) (S.vec a₁), hvec13, h13] at hmain
  exact absurd hmain (by decide)

private theorem mul_ne_one_and_quadQ_of_singular_pair (hZ : blockZ J = ⊥)
    {u₁ u₂ : ↥(blockU J)} (h1 : S.vec u₁ ≠ 0) (h2 : S.vec u₂ ≠ 0)
    (h12 : S.vec u₁ ≠ S.vec u₂) (hq1 : quadQ m (S.vec u₁) = 0)
    (hq2 : quadQ m (S.vec u₂) = 0) (hp : polar (quadQ m) (S.vec u₁) (S.vec u₂) = 0) :
    u₁ * u₂ ≠ 1 ∧ quadQ m (S.vec (u₁ * u₂)) = 0 := by
  constructor
  · intro h
    apply h12
    have hv : S.vec u₁ + S.vec u₂ = 0 := by rw [← S.vec_mul, h, S.vec_one]
    have h' : S.vec u₁ = -S.vec u₂ := eq_neg_of_add_eq_zero_left hv
    rwa [ZModModule.neg_eq_self] at h'
  · rw [S.vec_mul, QuadraticMap.map_add (quadQ m), hq1, hq2, hp]
    ring

theorem mem_of_conj_mem_of_singular_pair (hE : EvenCase J m) {u₁ u₂ : ↥(blockU J)}
    (h1 : S.vec u₁ ≠ 0) (h2 : S.vec u₂ ≠ 0) (h12 : S.vec u₁ ≠ S.vec u₂)
    (hq1 : quadQ m (S.vec u₁) = 0) (hq2 : quadQ m (S.vec u₂) = 0)
    (hp : polar (quadQ m) (S.vec u₁) (S.vec u₂) = 0) {z : G} (hz : z ∈ blockW J)
    (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) {g : G} (hg1 : g⁻¹ * (u₁ : G) * g ∈ pCoreOf 2 M)
    (hg2 : g⁻¹ * (u₂ : G) * g ∈ pCoreOf 2 M) (hgz : g⁻¹ * z * g ∈ pCoreOf 2 M) : g ∈ M := by
  classical
  by_contra hgM
  have hZ : blockZ J = ⊥ := S.blockZ_eq_bot hE.toBlockCase.h1
  have hu₁1 : u₁ ≠ 1 := fun h => h1 ((S.vec_eq_zero_iff hZ).mpr h)
  have hu₂1 : u₂ ≠ 1 := fun h => h2 ((S.vec_eq_zero_iff hZ).mpr h)
  obtain ⟨h121, hq12⟩ :=
    mul_ne_one_and_quadQ_of_singular_pair (S := S) hZ h1 h2 h12 hq1 hq2 hp
  obtain ⟨a₁, w₁, hw₁, heq₁⟩ :=
    exists_subtype_mul_of_mem_pCoreOf (S := S) hE.toBlockCase hg1
  obtain ⟨a₂, w₂, hw₂, heq₂⟩ :=
    exists_subtype_mul_of_mem_pCoreOf (S := S) hE.toBlockCase hg2
  obtain ⟨a₃, w₃, hw₃, heq₃⟩ :=
    exists_subtype_mul_of_mem_pCoreOf (S := S) hE.toBlockCase hgz
  have hQ₁ : quadQ m (S.vec a₁) = 1 :=
    quadQ_vec_eq_one_of_conj_mem_of_singular (S := S) hE hu₁1 hq1 (blockW J).one_mem hw₁
      (by simpa using heq₁) hgM
  have hQ₂ : quadQ m (S.vec a₂) = 1 :=
    quadQ_vec_eq_one_of_conj_mem_of_singular (S := S) hE hu₂1 hq2 (blockW J).one_mem hw₂
      (by simpa using heq₂) hgM
  have hQ₃ : quadQ m (S.vec a₃) = 1 :=
    quadQ_vec_eq_one_of_conj_mem_of_mem_blockW (S := S) hE hz hz1 hz2 hw₃
      (by simpa using heq₃) hgM
  have hQ₁₂ : quadQ m (S.vec (a₁ * a₂)) = 1 :=
    quadQ_vec_eq_one_of_conj_mul (S := S) hE h121 hq12 (blockW J).one_mem
      (blockW J).one_mem hw₁ hw₂ (by simpa using heq₁) (by simpa using heq₂) hgM
  have hQ₁₃ : quadQ m (S.vec (a₁ * a₃)) = 1 :=
    quadQ_vec_eq_one_of_conj_mul (S := S) hE (u := u₁) (u' := 1)
      (by simpa using hu₁1) (by simpa using hq1) (blockW J).one_mem hz hw₁ hw₃
      (by simpa using heq₁) (by simpa using heq₃) hgM
  have hQ₂₃ : quadQ m (S.vec (a₂ * a₃)) = 1 :=
    quadQ_vec_eq_one_of_conj_mul (S := S) hE (u := u₂) (u' := 1)
      (by simpa using hu₂1) (by simpa using hq2) (blockW J).one_mem hz hw₂ hw₃
      (by simpa using heq₂) (by simpa using heq₃) hgM
  have hprod12 : g⁻¹ * (((u₁ * u₂ : ↥(blockU J)) : G) * 1) * g =
      ((a₁ * a₂ : ↥(blockU J)) : G) * (w₁ * w₂) := by
    calc g⁻¹ * (((u₁ * u₂ : ↥(blockU J)) : G) * 1) * g
        = (g⁻¹ * (u₁ : G) * g) * (g⁻¹ * (u₂ : G) * g) := by
          rw [Subgroup.coe_mul]; group
      _ = ((a₁ : G) * w₁) * ((a₂ : G) * w₂) := by rw [heq₁, heq₂]
      _ = ((a₁ * a₂ : ↥(blockU J)) : G) * (w₁ * w₂) := mul_eq_mul_of_mem S hw₁ hw₂
  have hQ₁₂₃ : quadQ m (S.vec (a₁ * a₂ * a₃)) = 1 :=
    quadQ_vec_eq_one_of_conj_mul (S := S) hE (u := u₁ * u₂) (u' := 1)
      (by simpa using h121) (by simpa using hq12) (blockW J).one_mem hz
      ((blockW J).mul_mem hw₁ hw₂) hw₃ hprod12 (by simpa using heq₃) hgM
  exact quadQ_add_add_add_ne_one hQ₁ hQ₂ hQ₃ hQ₁₂ hQ₁₃ hQ₂₃ hQ₁₂₃

theorem mem_of_conj_mem_of_perp (hE : EvenCase J m) {b : ↥(blockU J)}
    (hb : quadQ m (S.vec b) = 1) {g : G}
    (hg : ∀ a : ↥(blockU J), polar (quadQ m) (S.vec a) (S.vec b) = 0 → ∀ w ∈ blockW J,
      g⁻¹ * ((a : G) * w) * g ∈ pCoreOf 2 M) : g ∈ M := by
  have hZ : blockZ J = ⊥ := S.blockZ_eq_bot hE.toBlockCase.h1
  obtain ⟨u₁, u₂, hu₁, hu₂, hu₁₂, hq₁, hq₂, hq₁₂, hpb₁, hpb₂⟩ :=
    exists_singular_pair_perp_blockU (S := S) hZ hb
  have hv₁ : S.vec u₁ ≠ 0 := fun h => hu₁ ((S.vec_eq_zero_iff hZ).mp h)
  have hv₂ : S.vec u₂ ≠ 0 := fun h => hu₂ ((S.vec_eq_zero_iff hZ).mp h)
  have hv₁₂ : S.vec u₁ ≠ S.vec u₂ := by
    intro h
    apply hu₁₂
    have hv : S.vec (u₁ * u₂) = 0 := by rw [S.vec_mul, h, ZModModule.add_self]
    exact (S.vec_eq_zero_iff hZ).mp hv
  have hp : polar (quadQ m) (S.vec u₁) (S.vec u₂) = 0 := by
    have h := hq₁₂
    rw [S.vec_mul, QuadraticMap.map_add (quadQ m), hq₁, hq₂] at h
    simpa using h
  obtain ⟨z, hz, hz1, hz2⟩ := exists_involution_blockW (J := J) (m := m) hE
  refine mem_of_conj_mem_of_singular_pair (S := S) hE hv₁ hv₂ hv₁₂ hq₁ hq₂ hp hz hz1 hz2
    ?_ ?_ ?_
  · simpa using hg u₁ hpb₁ 1 (blockW J).one_mem
  · simpa using hg u₂ hpb₂ 1 (blockW J).one_mem
  · simpa using hg 1 (by simp [S.vec_one]) z hz

theorem pCoreOf_centralizer_le_of_nonsingular (hE : EvenCase J m) {b : ↥(blockU J)}
    (hb : quadQ m (S.vec b) = 1) {w : G} (hw : w ∈ blockW J) :
    pCoreOf 2 (Subgroup.centralizer ({(b : G) * w} : Set G)) ≤ M :=
  pCoreOf_centralizer_le_of_perp (S := S) hE.toBlockCase hb hw
    (fun g hg => mem_of_conj_mem_of_perp (S := S) hE hb hg)

private theorem mem_of_conj_mem_of_nonsingular_ne (hE : EvenCase J m) {b : ↥(blockU J)}
    (hb : quadQ m (S.vec b) = 1) {w : G} (hw : w ∈ blockW J) {z : G} (hz : z ∈ blockW J)
    (hz1 : z ≠ 1) {g : G} (hg : g * z * g⁻¹ = (b : G) * w)
    (hne : (pCoreOf 2 M).map (MulAut.conj g).toMonoidHom ≠ pCoreOf 2 M) : g ∈ M := by
  let B : Subgroup G := (pCoreOf 2 M).map (MulAut.conj g).toMonoidHom
  have hB_eq : pCoreOf 2 (Subgroup.centralizer ({(b : G) * w} : Set G)) = B := by
    rw [pCoreOf_centralizer_conj (x := z) (y := (b : G) * w) (g := g) hg,
      pCoreOf_centralizer_eq (S := S) hE.toBlockCase hz hz1]
  have hBM : B ≤ M := by
    rw [← hB_eq]
    exact pCoreOf_centralizer_le_of_nonsingular (S := S) hE hb hw
  have hBab : ∀ p ∈ B, ∀ q ∈ B, p * q = q * p := by
    intro p hp q hq
    obtain ⟨p₀, hp₀, rfl⟩ := Subgroup.mem_map.mp hp
    obtain ⟨q₀, hq₀, rfl⟩ := Subgroup.mem_map.mp hq
    rw [← map_mul, ← map_mul, pCoreOf_comm (S := S) hE.toBlockCase hp₀ hq₀]
  have hB2 : IsPGroup 2 B :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).map (MulAut.conj g).toMonoidHom
  have hBt : ∀ t ∈ B, t * (b : G) * t⁻¹ = b := by
    intro t ht
    have htC : t ∈ pCoreOf 2 (Subgroup.centralizer ({(b : G) * w} : Set G)) := by
      rw [hB_eq]; exact ht
    exact conj_eq_of_mem_centralizer_mul (S := S) hE.toBlockCase hw (hBM ht)
      (by simpa using CFSG.LieType.BorelTits.pCoreOf_le 2 _ htC)
  have hBn : ∀ ℓ ∈ J, ℓ * (b : G) * ℓ⁻¹ = b → ∀ t ∈ B, ℓ * t * ℓ⁻¹ ∈ B := by
    intro ℓ hℓJ hℓb t ht
    have htC : t ∈ pCoreOf 2 (Subgroup.centralizer ({(b : G) * w} : Set G)) := by
      rw [hB_eq]; exact ht
    have hthis := conj_mem_pCoreOf_centralizer_of_centralizes (u := b) hw hℓJ hℓb htC
    rwa [hB_eq] at hthis
  have hcard : Nat.card (pCoreOf 2 M) ≤ Nat.card ↥B := by
    rw [Subgroup.card_map_of_injective (K := pCoreOf 2 M)
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
  have hperp : ∀ a : ↥(blockU J), polar (quadQ m) (S.vec a) (S.vec b) = 0 →
      ∀ w' ∈ blockW J, g⁻¹ * ((a : G) * w') * g ∈ pCoreOf 2 M := by
    intro a ha w' hw'
    have hmemB : (a : G) * w' ∈ B :=
      mul_mem_of_nonsingular (S := S) hE.toBlockCase hb hBM hB2 hBt hBn le_rfl hBab
        hcard hne ha hw'
    obtain ⟨v, hv, hveq⟩ := Subgroup.mem_map.mp hmemB
    have hc : g * v * g⁻¹ = (a : G) * w' := by
      simpa [MulAut.conj_apply] using hveq
    have hveq' : g⁻¹ * ((a : G) * w') * g = v := by rw [← hc]; group
    rwa [hveq']
  exact mem_of_conj_mem_of_perp (S := S) hE hb hperp

theorem conj_ne_of_nonsingular (hE : EvenCase J m) {b : ↥(blockU J)}
    (hb : quadQ m (S.vec b) = 1) {w : G} (hw : w ∈ blockW J) {z : G} (hz : z ∈ blockW J)
    (hz1 : z ≠ 1) (g : G) : g * z * g⁻¹ ≠ (b : G) * w := by
  intro hg
  have hZ : blockZ J = ⊥ := S.blockZ_eq_bot hE.toBlockCase.h1
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, S.vec_one, map_zero] at hb
    exact zero_ne_one hb
  have hcontra : g ∈ M → False := by
    intro hgM
    have hzW : (b : G) * w ∈ blockW J := by
      rw [← hg]; exact conj_mem_blockW S hgM hz
    exact mul_notMem_blockW S hZ hb1 hw hzW
  by_cases hBeq : (pCoreOf 2 M).map (MulAut.conj g).toMonoidHom = pCoreOf 2 M
  · apply hcontra
    have hgN : g ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hBeq
    rw [← CFSG.RankThree.PartTwo.Late.normalizer_pCoreOf_of_isMaximalTwoLocal S.maxLocal]
    exact hgN
  · exact hcontra (mem_of_conj_mem_of_nonsingular_ne (S := S) hE hb hw hz hz1 hg hBeq)

end CFSG.CGT.Harada80.Setting
