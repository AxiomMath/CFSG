module

public import CFSG.CGT.Harada80.Singular

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Harada80.Setting

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.RankThree.PartTwo QuadraticMap
open CFSG.ClassicalGroups.Orthogonal

variable {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ} {S : Setting G M J m}

private theorem exists_unique_mul_of_mem_pCoreOf (S : Setting G M J m) (hE : BlockCase J m)
    {x : G} (hx : x ∈ pCoreOf 2 M) :
    ∃! p : ↥(blockU J) × ↥(blockW J), x = (p.1 : G) * (p.2 : G) := by
  obtain ⟨a, ha, w, hw, rfl⟩ := exists_mul_of_mem_pCoreOf (S := S) hE hx
  refine ⟨(⟨a, ha⟩, ⟨w, hw⟩), rfl, ?_⟩
  rintro ⟨a', w'⟩ h
  obtain ⟨h1, h2⟩ := eq_of_mul_eq S (S.blockZ_eq_bot hE.h1) ha a'.2 hw w'.2 h
  exact Prod.ext (Subtype.ext h1.symm) (Subtype.ext h2.symm)

private theorem card_le_card_ker_mul_two (hZ : blockZ J = ⊥) {B : Subgroup G} (hBM : B ≤ M)
    {s : G} (hsB : s ∈ B) {r : Vec m ≃ₗ[ZMod 2] Vec m}
    (hsr : S.lin hZ ⟨s, hBM hsB⟩ = r)
    (hBr : ∀ x : ↥B, S.lin hZ ⟨(x : G), hBM x.2⟩ = 1 ∨
      S.lin hZ ⟨(x : G), hBM x.2⟩ = r) :
    Nat.card ↥B ≤ Nat.card ↥(B.subgroupOf M ⊓ (S.lin hZ).ker) * 2 := by
  let K : Subgroup ↥M := B.subgroupOf M ⊓ (S.lin hZ).ker
  let ψ : ↥K × Bool → ↥B := fun p =>
    match p.2 with
    | false => ⟨(p.1.1 : G), Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp p.1.2).1⟩
    | true => ⟨s * (p.1.1 : G), B.mul_mem hsB
        (Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp p.1.2).1)⟩
  have hψ : Function.Surjective ψ := by
    intro x
    have hxM : (⟨(x : G), hBM x.2⟩ : ↥M) ∈ B.subgroupOf M :=
      Subgroup.mem_subgroupOf.mpr x.2
    rcases hBr x with hx1 | hxr
    · refine ⟨(⟨⟨(x : G), hBM x.2⟩, Subgroup.mem_inf.mpr ⟨hxM, ?_⟩⟩, false), ?_⟩
      · exact MonoidHom.mem_ker.mpr hx1
      · exact Subtype.ext rfl
    · let kM : ↥M := ⟨s, hBM hsB⟩⁻¹ * ⟨(x : G), hBM x.2⟩
      have hkBM : kM ∈ B.subgroupOf M := by
        rw [Subgroup.mem_subgroupOf]
        simpa [kM] using B.mul_mem (B.inv_mem hsB) x.2
      have hkker : kM ∈ (S.lin hZ).ker := by
        rw [MonoidHom.mem_ker]
        have hmap : S.lin hZ kM = (S.lin hZ ⟨s, hBM hsB⟩)⁻¹ *
            S.lin hZ ⟨(x : G), hBM x.2⟩ := by
          simp only [kM, map_mul, map_inv]
        rw [hmap, hsr, hxr, inv_mul_cancel]
      refine ⟨(⟨kM, Subgroup.mem_inf.mpr ⟨hkBM, hkker⟩⟩, true), ?_⟩
      apply Subtype.ext
      show s * (kM : G) = (x : G)
      simp [kM]
  have h := Nat.card_le_card_of_surjective ψ hψ
  simpa [K, Nat.card_prod, Nat.card_eq_fintype_card] using h

private theorem polar_vec_eq_zero_of_commute (hE : BlockCase J m) (hZ : blockZ J = ⊥)
    {s : G} (hsM : s ∈ M) {b a : ↥(blockU J)} (hb : quadQ m (S.vec b) = 1)
    (hsr : S.lin hZ ⟨s, hsM⟩ = CFSG.ClassicalGroups.Orthogonal.reflect (quadQ m) (S.vec b))
    {w : G} (hw : w ∈ blockW J) (hcomm : s * ((a : G) * w) * s⁻¹ = (a : G) * w) :
    polar (quadQ m) (S.vec a) (S.vec b) = 0 := by
  have hsa : s * (a : G) * s⁻¹ = (a : G) :=
    ((conj_mul_eq_iff (S := S) hE hsM a.2 hw).mp hcomm).1
  have hfix : S.lin hZ ⟨s, hsM⟩ (S.vec a) = S.vec a :=
    (S.lin_vec_eq_iff hZ ⟨s, hsM⟩ a).mpr hsa
  rw [hsr] at hfix
  exact (reflect_apply_eq_self_iff hb).mp hfix

private theorem pCoreOf_of_mem_inf_ker (hE : BlockCase J m) (hZ : blockZ J = ⊥)
    {B : Subgroup G} (hBM : B ≤ M) (hB : IsPGroup 2 B) :
    ∀ x : ↥(B.subgroupOf M ⊓ (S.lin hZ).ker), (x.1 : G) ∈ pCoreOf 2 M := fun x =>
  mem_pCoreOf_of_lin_eq_one (S := S) hE hZ hBM hB
    (Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp x.2).1)
    (MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp x.2).2)

private theorem exists_injective_to_perp_times_W (hE : BlockCase J m) (hZ : blockZ J = ⊥)
    {B : Subgroup G} (hBM : B ≤ M) (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    {s : G} (hsB : s ∈ B) {b : ↥(blockU J)} (hb : quadQ m (S.vec b) = 1)
    (hsr : S.lin hZ ⟨s, hBM hsB⟩ =
      CFSG.ClassicalGroups.Orthogonal.reflect (quadQ m) (S.vec b))
    {K : Subgroup ↥M} (hK_B : ∀ x : ↥K, (x.1 : G) ∈ B)
    (hK_AW : ∀ x : ↥K, (x.1 : G) ∈ pCoreOf 2 M) :
    ∃ Φ : ↥K → {a : ↥(blockU J) // polar (quadQ m) (S.vec a) (S.vec b) = 0} ×
        ↥(blockW J),
      Function.Injective Φ ∧ ∀ x, (x.1 : G) = ((Φ x).1 : G) * ((Φ x).2 : G) := by
  classical
  have hpOf : ∀ x : ↥K, ∃! p : ↥(blockU J) × ↥(blockW J),
      (x.1 : G) = (p.1 : G) * (p.2 : G) :=
    fun x => exists_unique_mul_of_mem_pCoreOf S hE (hK_AW x)
  let pOf (x : ↥K) : ↥(blockU J) × ↥(blockW J) := Classical.choose (hpOf x)
  have pOf_spec (x : ↥K) : (x.1 : G) = (pOf x).1 * (pOf x).2 :=
    (Classical.choose_spec (hpOf x)).1
  have hcomm : ∀ x : ↥K, s * (x.1 : G) * s⁻¹ = (x.1 : G) := by
    intro x
    calc s * (x.1 : G) * s⁻¹ = ((x.1 : G) * s) * s⁻¹ := by rw [hB s hsB (x.1 : G) (hK_B x)]
      _ = (x.1 : G) := by group
  have hΦ_fst : ∀ x : ↥K, polar (quadQ m) (S.vec (pOf x).1) (S.vec b) = 0 := by
    intro x
    have hconj : s * ((pOf x).1 * (pOf x).2) * s⁻¹ = (pOf x).1 * (pOf x).2 := by
      rw [← pOf_spec x]
      exact hcomm x
    exact polar_vec_eq_zero_of_commute (S := S) hE hZ (hBM hsB) hb hsr (pOf x).2.2 hconj
  let Φ : ↥K → {a : ↥(blockU J) // polar (quadQ m) (S.vec a) (S.vec b) = 0} ×
      ↥(blockW J) := fun x => (⟨(pOf x).1, hΦ_fst x⟩, (pOf x).2)
  refine ⟨Φ, ?_, ?_⟩
  · intro x y hxy
    have h1 : ((pOf x).1 : G) = ((pOf y).1 : G) := by
      have h := congrArg (fun p => (p.1 : ↥(blockU J))) hxy
      exact congrArg Subtype.val h
    have h2 : ((pOf x).2 : G) = ((pOf y).2 : G) := by
      have h := congrArg (fun p => (p.2 : ↥(blockW J))) hxy
      exact congrArg Subtype.val h
    have hp : pOf x = pOf y := Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    apply Subtype.ext
    apply Subtype.ext
    calc ((x.1 : ↥M) : G) = (pOf x).1 * (pOf x).2 := pOf_spec x
      _ = (pOf y).1 * (pOf y).2 := by rw [hp]
      _ = ((y.1 : ↥M) : G) := (pOf_spec y).symm
  · exact pOf_spec

theorem lin_eq_one_or_eq_reflect (hZ : blockZ J = ⊥) {b : ↥(blockU J)}
    (hb : quadQ m (S.vec b) = 1) {T : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup 2 T)
    (hTb : ∀ t ∈ T, t * (b : G) * t⁻¹ = b)
    (hTn : ∀ ℓ ∈ J, ℓ * (b : G) * ℓ⁻¹ = b → ∀ t ∈ T, ℓ * t * ℓ⁻¹ ∈ T)
    {t : G} (ht : t ∈ T) :
    S.lin hZ ⟨t, hTM ht⟩ = 1 ∨
      S.lin hZ ⟨t, hTM ht⟩ = CFSG.ClassicalGroups.Orthogonal.reflect (quadQ m) (S.vec b) := by
  have h6 : 6 ≤ Module.finrank (ZMod 2) (Vec m) := by
    rw [CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.finrank_minus]
    rcases S.m_eq with h | h <;> omega
  have hfix : ∀ z, polar (quadQ m) z (S.vec b) = 0 →
      S.lin hZ ⟨t, hTM ht⟩ z = z := by
    intro z hz
    exact apply_eq_of_sub_mem_span_of_map_eq_one hb
      (S.lin_mem_orthogonalGroup hZ ⟨t, hTM ht⟩) hz
      (S.lin_sub_mem_span hZ
        (eq_span_or_eq_orth_of_map_eq_one (nondegenerate_quadQ m) h6 hb)
        hTM hT hTb hTn ht hz)
  exact CFSG.RankThree.Literature.FSmith.eq_one_or_eq_reflect_of_fix
    (nondegenerate_quadQ m) hb (S.lin_mem_orthogonalGroup hZ ⟨t, hTM ht⟩) hfix

private theorem lin_eq_reflect_of_not_mem_pCoreOf (hE : BlockCase J m) (hZ : blockZ J = ⊥)
    {b : ↥(blockU J)} (hb : quadQ m (S.vec b) = 1) {T : Subgroup G} (hTM : T ≤ M)
    (hT : IsPGroup 2 T) (hTb : ∀ t ∈ T, t * (b : G) * t⁻¹ = b)
    (hTn : ∀ ℓ ∈ J, ℓ * (b : G) * ℓ⁻¹ = b → ∀ t ∈ T, ℓ * t * ℓ⁻¹ ∈ T)
    {s : G} (hsT : s ∈ T) (hsNotAW : s ∉ pCoreOf 2 M) :
    S.lin hZ ⟨s, hTM hsT⟩ =
      CFSG.ClassicalGroups.Orthogonal.reflect (quadQ m) (S.vec b) := by
  rcases lin_eq_one_or_eq_reflect (S := S) hZ hb hTM hT hTb hTn hsT with h1 | h1
  · exact (hsNotAW (mem_pCoreOf_of_lin_eq_one (S := S) hE hZ hTM hT hsT h1)).elim
  · exact h1

theorem card_perp_mul_two {b : ↥(blockU J)} (hb : S.vec b ≠ 0) :
    Nat.card {a : ↥(blockU J) // polar (quadQ m) (S.vec a) (S.vec b) = 0} * 2 =
      Nat.card ↥(blockU J) := by
  classical
  let φ : ↥(blockU J) →* Multiplicative (ZMod 2) :=
    { toFun := fun a => Multiplicative.ofAdd (polar (quadQ m) (S.vec a) (S.vec b))
      map_one' := by rw [S.vec_one, QuadraticMap.polar_zero_left]; rfl
      map_mul' := fun a b => by rw [S.vec_mul, QuadraticMap.polar_add_left]; rfl }
  obtain ⟨v, hv⟩ := exists_polar_ne_zero (nondegenerate_quadQ m) hb
  have hv1 : polar (quadQ m) v (S.vec b) = 1 := by
    rw [polar_comm]
    exact CFSG.RankThree.Literature.FSmith.zmod2_eq_one_of_ne_zero hv
  have hφ : Function.Surjective φ := by
    intro c
    rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one c.toAdd with h | h
    · refine ⟨1, ?_⟩
      apply Multiplicative.toAdd.injective
      show polar (quadQ m) (S.vec 1) (S.vec b) = c.toAdd
      rw [S.vec_one, h]
      simp
    · obtain ⟨a, ha⟩ := S.vec_surjective v
      refine ⟨a, ?_⟩
      apply Multiplicative.toAdd.injective
      show polar (quadQ m) (S.vec a) (S.vec b) = c.toAdd
      rw [ha, hv1, h]
  have hker : Nat.card {a : ↥(blockU J) // polar (quadQ m) (S.vec a) (S.vec b) = 0} =
      Nat.card ↥φ.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun a => by
      show polar (quadQ m) (S.vec a) (S.vec b) = 0 ↔
        Multiplicative.ofAdd (polar (quadQ m) (S.vec a) (S.vec b)) = 1
      rw [ofAdd_eq_one])
  calc Nat.card {a : ↥(blockU J) // polar (quadQ m) (S.vec a) (S.vec b) = 0} * 2
      = Nat.card ↥φ.ker * 2 := by rw [hker]
    _ = Nat.card ↥(blockU J) := by
        have h := Subgroup.card_ker_mul_card_of_surjective (f := φ) hφ
        rw [show Nat.card (Multiplicative (ZMod 2)) = 2 by
          rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]] at h
        exact h

private theorem card_perp_times_W_le_card (hE : BlockCase J m) {b : ↥(blockU J)}
    (hb0 : S.vec b ≠ 0) {B : Subgroup G} {K : Subgroup ↥M}
    (hcard : Nat.card (pCoreOf 2 M) ≤ Nat.card B)
    (hBleK : Nat.card ↥B ≤ Nat.card ↥K * 2)
    (hKle : Nat.card ↥K ≤
      Nat.card {a : ↥(blockU J) // polar (quadQ m) (S.vec a) (S.vec b) = 0} *
        Nat.card ↥(blockW J)) :
    Nat.card ({a : ↥(blockU J) // polar (quadQ m) (S.vec a) (S.vec b) = 0} ×
      ↥(blockW J)) ≤ Nat.card ↥K := by
  have hA2 := card_perp_mul_two (S := S) hb0
  have hAWcard := card_pCoreOf (S := S) hE
  have hA2W2 : (Nat.card {a : ↥(blockU J) // polar (quadQ m) (S.vec a) (S.vec b) = 0} *
      Nat.card ↥(blockW J)) * 2 ≤ Nat.card ↥K * 2 := by
    calc (Nat.card {a : ↥(blockU J) // polar (quadQ m) (S.vec a) (S.vec b) = 0} *
          Nat.card ↥(blockW J)) * 2
        = (Nat.card {a : ↥(blockU J) // polar (quadQ m) (S.vec a) (S.vec b) = 0} * 2) *
            Nat.card ↥(blockW J) := by ring
      _ = Nat.card ↥(blockU J) * Nat.card ↥(blockW J) := by rw [hA2]
      _ = Nat.card (pCoreOf 2 M) := hAWcard.symm
      _ ≤ Nat.card ↥B := hcard
      _ ≤ Nat.card ↥K * 2 := hBleK
  rw [Nat.card_prod]
  exact Nat.le_of_mul_le_mul_right hA2W2 (by norm_num : 0 < 2)

theorem mul_mem_of_nonsingular (hE : BlockCase J m) {b : ↥(blockU J)}
    (hb : quadQ m (S.vec b) = 1) {T : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup 2 T)
    (hTb : ∀ t ∈ T, t * (b : G) * t⁻¹ = b)
    (hTn : ∀ ℓ ∈ J, ℓ * (b : G) * ℓ⁻¹ = b → ∀ t ∈ T, ℓ * t * ℓ⁻¹ ∈ T)
    {B : Subgroup G} (hBT : B ≤ T) (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hcard : Nat.card (pCoreOf 2 M) ≤ Nat.card B) (hne : B ≠ pCoreOf 2 M)
    {a : ↥(blockU J)} (ha : polar (quadQ m) (S.vec a) (S.vec b) = 0) {w : G}
    (hw : w ∈ blockW J) : (a : G) * w ∈ B := by
  classical
  have hZ : blockZ J = ⊥ := S.blockZ_eq_bot hE.h1
  have hb0 : S.vec b ≠ 0 := fun h => by
    rw [h, map_zero] at hb
    exact zero_ne_one hb
  obtain ⟨s, hsB, hsNotAW⟩ : ∃ s ∈ B, s ∉ pCoreOf 2 M := by
    by_contra hcon
    push Not at hcon
    exact (fun hle => hne (Subgroup.eq_of_le_of_card_ge hle hcard)) fun x hx => hcon x hx
  have hBM : B ≤ M := fun x hx => hTM (hBT hx)
  have hsLin : S.lin hZ ⟨s, hBM hsB⟩ =
      CFSG.ClassicalGroups.Orthogonal.reflect (quadQ m) (S.vec b) :=
    lin_eq_reflect_of_not_mem_pCoreOf (S := S) hE hZ hb hTM hT hTb hTn (hBT hsB) hsNotAW
  let K : Subgroup ↥M := B.subgroupOf M ⊓ (S.lin hZ).ker
  have hBleK : Nat.card ↥B ≤ Nat.card ↥K * 2 :=
    card_le_card_ker_mul_two (S := S) hZ hBM hsB hsLin fun x =>
      lin_eq_one_or_eq_reflect (S := S) hZ hb hTM hT hTb hTn (hBT x.2)
  have hK_B : ∀ x : ↥K, (x.1 : G) ∈ B :=
    fun x => Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp x.2).1
  have hK_AW : ∀ x : ↥K, (x.1 : G) ∈ pCoreOf 2 M :=
    pCoreOf_of_mem_inf_ker (S := S) hE hZ hBM (hT.to_le hBT)
  obtain ⟨Φ, hΦinj, hΦspec⟩ :=
    exists_injective_to_perp_times_W (S := S) hE hZ hBM hB hsB hb hsLin hK_B hK_AW
  have hKle : Nat.card ↥K ≤
      Nat.card {a : ↥(blockU J) // polar (quadQ m) (S.vec a) (S.vec b) = 0} *
        Nat.card ↥(blockW J) := by
    have h := Nat.card_le_card_of_injective Φ hΦinj
    simpa [Nat.card_prod] using h
  have hcard_le : Nat.card ({a : ↥(blockU J) //
      polar (quadQ m) (S.vec a) (S.vec b) = 0} × ↥(blockW J)) ≤ Nat.card ↥K :=
    card_perp_times_W_le_card (S := S) hE hb0 hcard hBleK hKle
  let A2 : {a : ↥(blockU J) // polar (quadQ m) (S.vec a) (S.vec b) = 0} := ⟨a, ha⟩
  obtain ⟨x, hx⟩ := (hΦinj.bijective_of_nat_card_le hcard_le).2 (A2, ⟨w, hw⟩)
  have hxval : (x.1 : G) = (a : G) * w := by
    calc (x.1 : G) = ((Φ x).1 : G) * ((Φ x).2 : G) := hΦspec x
      _ = (a : G) * w := by
        rw [congrArg (fun p => ((p.1 : ↥(blockU J)) : G)) hx,
          congrArg (fun p => ((p.2 : ↥(blockW J)) : G)) hx]
  have hxB : (x.1 : G) ∈ B := hK_B x
  rwa [← hxval]

end CFSG.CGT.Harada80.Setting
