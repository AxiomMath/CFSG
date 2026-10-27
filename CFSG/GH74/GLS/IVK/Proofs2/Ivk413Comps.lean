module

public import CFSG.GH74.GLS.Stage2.Final.ModelCenAb
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.Ivk413

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Final CFSG.GH74.GLS.Stage2.Final.ModelBlock
  CFSG.GH74.L5U5

variable {F : Type} [Field F]

theorem only_comps' [Finite F] {M : ModelData F} (hG : GoodModel M) {L : Subgroup (PG M)}
    (hcomp : IsCompIn (Cg M) L) : L = K1 M ∨ L = K2 M := by
  have hK1 := isCompIn_K1 hG
  have hK2 := isCompIn_K2 hG
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hn1, hn2⟩ := hne
  have hsub : ∀ {A : Subgroup (PG M)}, A ≤ Cg M → A ≠ L →
      A.subgroupOf (Cg M) ≠ L.subgroupOf (Cg M) := fun {A} hA hAL h => by
    apply hAL
    have := Subgroup.subgroupOf_inj.1 h
    rwa [inf_eq_left.2 hA, inf_eq_left.2 hcomp.1] at this
  have hcomm : ∀ {A : Subgroup (PG M)}, IsCompIn (Cg M) A → A ≠ L →
      ∀ l ∈ L, ∀ e ∈ A, l * e = e * l := by
    intro A hA hAL l hl e he
    rcases CFSG.LocalCores.distinct_components_commute hcomp.2 hA.2 with h | h
    · exact absurd h.symm (hsub hA.1 hAL)
    · have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
      have hl' : (⟨l, hcomp.1 hl⟩ : ↥(Cg M)) ∈ L.subgroupOf (Cg M) := hl
      have he' : (⟨e, hA.1 he⟩ : ↥(Cg M)) ∈ A.subgroupOf (Cg M) := he
      have := Subgroup.mem_centralizer_iff.1 (hle hl') ⟨e, hA.1 he⟩ he'
      exact (congrArg Subtype.val this).symm
  have hBS : ∀ l ∈ L, l ∈ BSsub M := by
    intro l hl
    have hle : K1 M ⊔ K2 M ≤ Subgroup.centralizer {l} :=
      sup_le (fun e he => Subgroup.mem_centralizer_singleton_iff.2
          (hcomm hK1 (fun h => hn1 h.symm) l hl e he).symm)
        (fun e he => Subgroup.mem_centralizer_singleton_iff.2
          (hcomm hK2 (fun h => hn2 h.symm) l hl e he).symm)
    obtain ⟨p, hp⟩ := blockScalar_of_cent_E hG (hcomp.1 hl) (fun e he =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hle he)).symm)
    exact ⟨p, hp⟩
  have hcyc : IsCyclic ↥(BSsub M) := isCyclic_BSsub M
  have hab : ∀ l ∈ L, ∀ l' ∈ L, l * l' = l' * l := by
    intro l hl l' hl'
    let _inst : CommGroup ↥(BSsub M) := IsCyclic.commGroup
    have := mul_comm (⟨l, hBS l hl⟩ : ↥(BSsub M)) ⟨l', hBS l' hl'⟩
    exact congrArg Subtype.val this
  have hcentral : L.subgroupOf (Cg M) ≤
      Subgroup.centralizer ((L.subgroupOf (Cg M) : Subgroup ↥(Cg M)) : Set ↥(Cg M)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subtype.ext (hab b hb a ha)
  have hcb : ⁅L.subgroupOf (Cg M), L.subgroupOf (Cg M)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcentral
  have hperf := Subgroup.isPerfect_iff.1 hcomp.2.1.1
  rw [hcb] at hperf
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hcomp.2.1
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥(L.subgroupOf (Cg M)))
  apply hx
  have hxm : (x : ↥(Cg M)) ∈ (⊥ : Subgroup ↥(Cg M)) := by
    rw [hperf]
    exact x.2
  exact Subtype.ext (Subgroup.mem_bot.1 hxm)

theorem mem_K1_iff_conj_tP (M : ModelData F) (y : PG M) :
    y ∈ K1 M ↔ tP M * y * (tP M)⁻¹ ∈ K2 M := by
  rw [← tP_swap M, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨y, h, by simp [MulAut.conj_apply]⟩
  · rintro ⟨w, hw, hwy⟩
    have : w = y := by
      have h' : tP M * w * (tP M)⁻¹ = tP M * y * (tP M)⁻¹ := by
        simpa [MulAut.conj_apply] using hwy
      exact mul_left_cancel (mul_right_cancel h')
    exact this ▸ hw

theorem normalizer_K2_le_C0 [Finite F] {M : ModelData F} (hG : GoodModel M) {s : PG M}
    (hs : s ∈ Subgroup.normalizer (K2 M : Set (PG M))) : s ∈ C0 M := by
  have h2 := hG.two_ne_zero
  set t := tP M with ht
  have hs' : t⁻¹ * s * t ∈ Subgroup.normalizer (K1 M : Set (PG M)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have e : t * ((t⁻¹ * s * t) * x * (t⁻¹ * s * t)⁻¹) * t⁻¹ = s * (t * x * t⁻¹) * s⁻¹ := by
      group
    rw [mem_K1_iff_conj_tP M x, mem_K1_iff_conj_tP M, e]
    exact (Subgroup.mem_normalizer_iff.1 hs _)
  have hs1 : t⁻¹ * s * t ∈ C0 M := normalizer_K1_le_C0 hG hs'
  have hCg : t⁻¹ * s * t ∈ Cg M := C0_le_Cg M hs1
  have hnorm : ((C0 M).subgroupOf (Cg M)).Normal :=
    Subgroup.normal_of_index_eq_two (index_C0_Cg M h2)
  have hm : (⟨t⁻¹ * s * t, hCg⟩ : ↥(Cg M)) ∈ (C0 M).subgroupOf (Cg M) := hs1
  have := hnorm.conj_mem _ hm ⟨t, tP_mem_Cg M⟩
  have e2 : t * (t⁻¹ * s * t) * t⁻¹ = s := by group
  rw [mem_subgroupOf] at this
  simpa [e2] using this

theorem bs_comm_C0 [Finite F] {M : ModelData F} (hG : GoodModel M) {c x : PG M}
    (hc : c ∈ BSsub M) (hx : x ∈ C0 M) : c * x = x * c := by
  have h2 := hG.two_ne_zero
  obtain ⟨⟨⟨l, m⟩, hp⟩, rfl⟩ := hc
  obtain ⟨n, hn, rfl⟩ := hx
  obtain ⟨a, b, hab, ha, hb, hdet⟩ := M.exists_diagGL_of_comm h2 n.2
    (congrArg Subtype.val (mem_Dsub.1 hn))
  show mkP M (bscK M ⟨(l, m), hp⟩) * mkP M n = mkP M n * mkP M (bscK M ⟨(l, m), hp⟩)
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show diagGL (sc2 l) (sc2 m) * (n : GL (Fin 4) F) = (n : GL (Fin 4) F) * diagGL (sc2 l) (sc2 m)
  rw [hab, diagGL_mul, diagGL_mul]
  congr 1
  · exact (Subgroup.mem_center_iff.1 (by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨l, rfl⟩) a).symm
  · exact (Subgroup.mem_center_iff.1 (by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨m, rfl⟩) b).symm

theorem odd_normal_K1 [Finite F] {M : ModelData F} (hG : GoodModel M) (N : Subgroup (PG M))
    (hNK : N ≤ K1 M) (hn : ∀ k ∈ K1 M, ∀ n ∈ N, k * n * k⁻¹ ∈ N) (hodd : Odd (Nat.card N)) :
    N = ⊥ := by
  let N'' : Subgroup ↥M.H2 := N.comap (iota1 M)
  have hnorm : N''.Normal := ⟨fun h hh g => by
    show iota1 M (g * h * g⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact hn _ ⟨g, rfl⟩ _ hh⟩
  have hmap : N''.map (iota1 M) = N := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hx
      obtain ⟨a, rfl⟩ := hNK hx
      exact ⟨a, hx, rfl⟩
  have hodd' : Odd (Nat.card N'') := by
    have := Subgroup.card_map_of_injective (K := N'') (iota1_injective M)
    rw [hmap] at this
    rwa [← this]
  have hbot : N'' = ⊥ := ModelGT.normal_odd_eq_bot hG.qs hG.center2 hG.even N'' hodd'
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨a, rfl⟩ := hNK hx
  have : a ∈ N'' := hx
  rw [hbot, Subgroup.mem_bot] at this
  rw [this, map_one]
  exact Subgroup.one_mem _

theorem det_sc2 (l : Fˣ) :
    ((sc2 l : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = (l : F) ^ 2 := by
  simp [sc2, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal, sq]

theorem bs_sq_sp {c : PG (ModelData.sp F)} (hc : c ∈ BSsub (ModelData.sp F)) : c * c = 1 := by
  obtain ⟨⟨⟨l, m⟩, hp⟩, rfl⟩ := hc
  have hK : diagGL (sc2 l) (sc2 m) ∈ (ModelData.sp F).K4 := hp
  obtain ⟨hl, hm, -⟩ := (ModelData.sp F).diagGL_mem_K4_iff.1 hK
  have hl' : (sc2 l : GL (Fin 2) F) ∈ (ModelData.sp F).H2 := by
    rw [ModelSp.H2_sp_eq_U2]; exact hl
  have hm' : (sc2 m : GL (Fin 2) F) ∈ (ModelData.sp F).H2 := by
    rw [ModelSp.H2_sp_eq_U2]; exact hm
  have hdl := ((ModelData.sp F).mem_H2 _).1 hl'
  have hdm := ((ModelData.sp F).mem_H2 _).1 hm'
  rw [det_sc2] at hdl hdm
  show mkP _ (bscK _ ⟨(l, m), hp⟩) * mkP _ (bscK _ ⟨(l, m), hp⟩) = 1
  rw [← map_mul]
  have : bscK (ModelData.sp F) ⟨(l, m), hp⟩ * bscK (ModelData.sp F) ⟨(l, m), hp⟩ = 1 := by
    apply Subtype.ext
    show diagGL (sc2 l) (sc2 m) * diagGL (sc2 l) (sc2 m) = 1
    rw [diagGL_mul, sc2_mul, sc2_mul]
    have h1 : l * l = 1 := Units.ext (by simpa [sq] using hdl.2)
    have h2 : m * m = 1 := Units.ext (by simpa [sq] using hdm.2)
    rw [h1, h2, sc2_one, diagGL_one]
  rw [this, map_one]

theorem pPrimeCoreOf_sp_eq_bot [Finite F] (h2 : (2 : F) ≠ 0) (h5 : 5 ≤ Nat.card F) :
    pPrimeCoreOf 2 (Cg (ModelData.sp F)) = ⊥ := by
  have hG := goodModel_sp h2 h5
  refine eq_bot_iff.2 fun x hx => ?_
  have hxB := pPrimeCoreOf_le_BS hG hx
  have hsq := bs_sq_sp hxB
  have hodd : Odd (orderOf x) :=
    Odd.of_dvd_nat (odd_card_pPrimeCoreOf _) (Subgroup.orderOf_dvd_natCard _ hx)
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [sq] using hsq)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · rw [orderOf_eq_one_iff.1 h]
    exact Subgroup.one_mem _
  · rw [h] at hodd
    exact absurd hodd (by decide)

end CFSG.GH74.Ivk413
