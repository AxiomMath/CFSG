module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.NonConstrainedStructure
public import CFSG.LocalAnalysis.QuasithinUnique.SteinbergCHAltSevenThreePlane
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.AGLEmbedding
open scoped Pointwise

theorem false_of_normal_a6_odd_index {X : Type*} [Group X] [Finite X] (N W Q : Subgroup X)
    [N.Normal] (hs : IsSimpleGroup ↥N) (hN : Nat.card N = 360) (hQN : Q ≤ N)
    (hQ : Nat.card Q = 9) (hQW : Q ≤ W) (hodd : ¬ 2 ∣ W.index) (h5 : ¬ 5 ∣ Nat.card W) :
    False := by
  have h9 : 9 ∣ Nat.card (W ⊓ N : Subgroup X) := by
    rw [← hQ]
    exact Subgroup.card_dvd_of_le (le_inf hQW hQN)
  have hcs := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_normal W N
  have hr := Subgroup.relIndex_mul_card (H := W) (K := W ⊔ N)
  rw [inf_of_le_left (le_sup_left : W ≤ W ⊔ N)] at hr
  have hri := Subgroup.relIndex_mul_index (le_sup_left : W ≤ W ⊔ N)
  have hrodd : ¬ 2 ∣ W.relIndex (W ⊔ N) := fun h => hodd (hri ▸ Dvd.dvd.mul_right h _)
  have hWpos : 0 < Nat.card W := Nat.card_pos
  have key : W.relIndex (W ⊔ N) * Nat.card (W ⊓ N : Subgroup X) = 360 := by
    have h : Nat.card W * (W.relIndex (W ⊔ N) * Nat.card (W ⊓ N : Subgroup X)) =
        Nat.card W * 360 := by
      rw [← hN, ← hcs, ← hr]
      ring
    exact Nat.eq_of_mul_eq_mul_left hWpos h
  obtain ⟨c, hc⟩ := h9
  obtain ⟨r, hrdef⟩ : ∃ r, r = W.relIndex (W ⊔ N) := ⟨_, rfl⟩
  rw [← hrdef] at key hrodd
  rw [hc] at key
  have hrc40 : r * c = 40 := by
    have h : 9 * (r * c) = 9 * 40 := by linarith
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hrc : r ∣ 40 := ⟨c, hrc40.symm⟩
  have hr40 : r ≤ 40 := Nat.le_of_dvd (by norm_num) hrc
  have hr15 : r = 1 ∨ r = 5 := by
    interval_cases r <;> omega
  rcases hr15 with h1 | h5'
  · rw [h1] at key
    have hb : Nat.card (W ⊓ N : Subgroup X) = Nat.card N := by omega
    have hNW : N ≤ W := by
      have := Subgroup.eq_of_le_of_card_ge (inf_le_right : W ⊓ N ≤ N) hb.ge
      exact this ▸ inf_le_left
    apply h5
    exact (by rw [hN]; norm_num : 5 ∣ Nat.card N).trans (Subgroup.card_dvd_of_le hNW)
  · rw [h5'] at key
    have hb : Nat.card (W ⊓ N : Subgroup X) = 72 := by omega
    have hsub : Nat.card ((W ⊓ N).subgroupOf N) = 72 := by
      rw [← hb]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    exact CFSG.QuasithinUnique.SteinbergCH.no_index_five_of_simple hN _ hsub

theorem mem_sup_centralizer_of_pow_three {X : Type*} [Group X] (N : Subgroup X) [N.Normal]
    (e : ↥N ≃* alternatingGroup (Fin 6)) {q : X} (hq : q ^ 3 = 1) :
    q ∈ N ⊔ Subgroup.centralizer (N : Set X) := by
  set f : MulAut ↥N := MulAut.conjNormal (H := N) q with hf
  have hf3 : f ^ 3 = 1 := by
    rw [hf, ← map_pow, hq, map_one]
  have hodd : Odd (orderOf (MulAut.congr e f)) := by
    rw [MulEquiv.orderOf_eq]
    exact (Nat.odd_iff.mpr (by norm_num : 3 % 2 = 1)).of_dvd_nat (orderOf_dvd_of_pow_eq_one hf3)
  obtain ⟨a, ha⟩ := CFSG.AGLEmbedding.mem_range_conj_of_odd_orderOf _ hodd
  set n : ↥N := e.symm a with hn
  have hfm : ∀ m : ↥N, f m = n * m * n⁻¹ := by
    intro m
    have h1 := congrArg (fun φ : MulAut (alternatingGroup (Fin 6)) => φ (e m)) ha
    simp only [MulAut.conj_apply, MulAut.congr_apply] at h1
    apply e.injective
    simp only [map_mul, map_inv, hn, MulEquiv.apply_symm_apply]
    rw [h1]
    simp
  have hc : (n : X)⁻¹ * q ∈ Subgroup.centralizer (N : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h := hfm ⟨m, hm⟩
    have h' : q * m * q⁻¹ = (n : X) * m * (n : X)⁻¹ := by
      have := congrArg Subtype.val h
      simpa [hf, MulAut.conjNormal_apply] using this
    calc m * ((n : X)⁻¹ * q) = (n : X)⁻¹ * ((n : X) * m * (n : X)⁻¹) * q := by group
      _ = (n : X)⁻¹ * (q * m * q⁻¹) * q := by rw [h']
      _ = (n : X)⁻¹ * q * m := by group
  have : q = (n : X) * ((n : X)⁻¹ * q) := by group
  rw [this]
  exact Subgroup.mul_mem_sup n.2 hc

theorem false_of_a6_faithful {X : Type*} [Group X] [Finite X] (N Q W : Subgroup X) [N.Normal]
    (hs : IsSimpleGroup ↥N) (e : ↥N ≃* alternatingGroup (Fin 6))
    (hQ3 : IsElemAbelian 3 Q) (hQ9 : Nat.card Q = 9)
    (hQC : Q ⊓ Subgroup.centralizer (N : Set X) = ⊥) (hQW : Q ≤ W) (hodd : ¬ 2 ∣ W.index)
    (h5 : ¬ 5 ∣ Nat.card W) : False := by
  set C := Subgroup.centralizer (N : Set X) with hC
  have hCn : C.Normal := inferInstance
  set π := QuotientGroup.mk' C with hπ
  have hker : π.ker = C := QuotientGroup.ker_mk' C
  have hNC : N ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hc6 : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
      alternatingGroup.center_eq_bot (by simp)
    have hex : e ⟨x, hx.1⟩ ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro b
      have hb := Subgroup.mem_centralizer_iff.mp hx.2 (e.symm b : X) (e.symm b).2
      have : e.symm b * (⟨x, hx.1⟩ : ↥N) = (⟨x, hx.1⟩ : ↥N) * e.symm b := Subtype.ext hb
      have h2 := congrArg e this
      simpa using h2
    rw [hc6, Subgroup.mem_bot] at hex
    have := e.injective (hex.trans (map_one e).symm)
    exact congrArg Subtype.val this
  have hfN : Function.Injective (π.comp N.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxC : (x : X) ∈ C := by
      have : π (x : X) = 1 := hx
      rw [← hker]
      exact this
    have : (x : X) ∈ N ⊓ C := ⟨x.2, hxC⟩
    rw [hNC, Subgroup.mem_bot] at this
    exact Subtype.ext (by simpa using this)
  have hrange : (π.comp N.subtype).range = N.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eN : ↥N ≃* ↥(N.map π) :=
    (MonoidHom.ofInjective hfN).trans (MulEquiv.subgroupCongr hrange)
  have hNhat : (N.map π).Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective C)
  have hsimp : IsSimpleGroup ↥(N.map π) := MulEquiv.isSimpleGroup eN.symm
  have hcard : Nat.card (N.map π) = 360 := by
    rw [← Nat.card_congr eN.toEquiv, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
      card_alternatingGroup]
    simp [Nat.factorial]
  have hQinj : Set.InjOn π (Q : Set X) := by
    intro x hx y hy hxy
    have : x⁻¹ * y ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    rw [hker] at this
    have h2 : x⁻¹ * y ∈ Q ⊓ C := ⟨Q.mul_mem (Q.inv_mem hx) hy, this⟩
    rw [hQC, Subgroup.mem_bot] at h2
    exact (inv_mul_eq_one.mp h2)
  have hQcard : Nat.card (Q.map π) = 9 := by
    rw [← hQ9]
    exact Nat.card_image_of_injOn hQinj
  have hQN : Q.map π ≤ N.map π := by
    rintro _ ⟨q, hq, rfl⟩
    have h3 : q ^ 3 = 1 := hQ3.2 q hq
    have hmem := mem_sup_centralizer_of_pow_three N e h3
    have hmem' : q ∈ (((N ⊔ C : Subgroup X)) : Set X) := hmem
    rw [Subgroup.normal_mul] at hmem'
    obtain ⟨n, hn, c, hc, hq'⟩ := Set.mem_mul.mp hmem'
    refine ⟨n, hn, ?_⟩
    have : π c = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hc
    rw [← hq', map_mul, this, mul_one]
  have hQW' : Q.map π ≤ W.map π := Subgroup.map_mono hQW
  have hodd' : ¬ 2 ∣ (W.map π).index := fun h =>
    hodd (h.trans (Subgroup.index_map_dvd W (QuotientGroup.mk'_surjective C)))
  have h5' : ¬ 5 ∣ Nat.card (W.map π) := fun h => h5 (h.trans (Subgroup.card_map_dvd W π))
  exact false_of_normal_a6_odd_index (N.map π) (W.map π) (Q.map π) hsimp hcard hQN hQcard hQW'
    hodd' h5'

@[expose] def KFactRankTwoE9 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (N Q : Subgroup X) [N.Normal], IsSimpleGroup ↥N →
    IsRankTwoLayerType ↥N → IsElemAbelian 3 Q → Nat.card Q = 9 →
    Q ⊓ Subgroup.centralizer (N : Set X) = ⊥ →
    (∀ x ∈ Q, ∀ y ∈ Q, x ≠ 1 → y ≠ 1 → ∃ g ∈ Subgroup.normalizer (Q : Set X), g * x * g⁻¹ = y) →
    Nonempty (↥N ≃* alternatingGroup (Fin 6))

theorem le_centralizer_of_odd_index {X : Type} [Group X] [Finite X] (hK : KFactRankTwoE9)
    (N Q W : Subgroup X) [N.Normal] (hs : IsSimpleGroup ↥N) (hty : IsRankTwoLayerType ↥N)
    (hQ3 : IsElemAbelian 3 Q) (hQ9 : Nat.card Q = 9)
    (htrans : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ 1 → y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (Q : Set X), g * x * g⁻¹ = y)
    (hQW : Q ≤ W) (hodd : ¬ 2 ∣ W.index) (h5 : ¬ 5 ∣ Nat.card W) :
    Q ≤ Subgroup.centralizer (N : Set X) := by
  set C := Subgroup.centralizer (N : Set X) with hC
  have hCn : C.Normal := inferInstance
  by_contra hQC
  have hK0 : Q ⊓ C = ⊥ := by
    by_contra hne
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    apply hQC
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1]; exact C.one_mem
    · obtain ⟨g, -, hg⟩ := htrans (x : X) x.2.1 y hy (by simpa using hx1) hy1
      rw [← hg]
      exact hCn.conj_mem _ x.2.2 g
  obtain ⟨e⟩ := hK X N Q hs hty hQ3 hQ9 hK0 htrans
  exact false_of_a6_faithful N Q W hs e hQ3 hQ9 hK0 hQW hodd h5

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
