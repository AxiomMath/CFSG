module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Proof
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFactsA6
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Case2Coord
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Case2Sylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Case2Img
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Case2W
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43E9R
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43E9Core

@[expose] public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Core

open CFSG.Open CFSG.ABGLocalTools CFSG.Quasithin CFSG.GH74.Exceptional Subgroup
  CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Aux CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Img
  CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6W
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_conj {p : ℕ} {A : Subgroup G} (hA : IsElemAbelian p A) (g : G) :
    IsElemAbelian p (A.map (MulAut.conj g).toMonoidHom) := by
  haveI := hA.1
  refine ⟨IsMulCommutative.of_setLike_mul_comm fun a ha b hb => ?_, fun z hz => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := ha
    obtain ⟨v, hv, rfl⟩ := hb
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * u * g⁻¹ * (g * v * g⁻¹) = g * (u * v) * g⁻¹ := by group
      _ = g * (v * u) * g⁻¹ := by rw [setLike_mul_comm hu hv]
      _ = g * v * g⁻¹ * (g * u * g⁻¹) := by group
  · obtain ⟨u, hu, rfl⟩ := hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_pow, hA.2 u hu]
    group

theorem mem_normalizer_of_map_le {S : Subgroup G} {y : G}
    (h : S.map (MulAut.conj y).toMonoidHom ≤ S) : y ∈ normalizer (S : Set G) := by
  have heq : S.map (MulAut.conj y).toMonoidHom = S := by
    apply Subgroup.eq_of_le_of_card_ge h
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
  refine mem_normalizer_iff.mpr fun z => ⟨fun hz => h ⟨z, hz, rfl⟩, fun hz => ?_⟩
  have h1 : y * z * y⁻¹ ∈ S.map (MulAut.conj y).toMonoidHom := by rw [heq]; exact hz
  obtain ⟨w, hw, hwz⟩ := h1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hwz
  have h2 : w = z := mul_left_cancel (mul_right_cancel hwz)
  rwa [← h2]

section Lines

variable {M O : Subgroup G} {x e₂ e₃ t ρ : G} {s : ℤ} (hf : A6VIFrame M O x e₂ e₃ t ρ s)

include hf

theorem conj_line {x' : G} (hx'ℓ : x' = x ∨ x' = e₂ ∨ x' = e₃) (h : G)
    (hh : h * x' * h⁻¹ ∈ Qf x e₂ e₃) :
    h * x' * h⁻¹ ∈ zpowers x ∨ h * x' * h⁻¹ ∈ zpowers e₂ ∨ h * x' * h⁻¹ ∈ zpowers e₃ := by
  rcases hx'ℓ with h1 | h1 | h1
  · rw [h1] at hh ⊢
    exact hf.lines h hh
  · have e : h * x' * h⁻¹ = (h * t) * x * (h * t)⁻¹ := by rw [h1, ← hf.t_x]; group
    rw [e] at hh ⊢
    exact hf.lines _ hh
  · have e : h * x' * h⁻¹ = (h * (t * t)) * x * (h * (t * t))⁻¹ := by
      rw [h1, hf.e₃_eq]; group
    rw [e] at hh ⊢
    exact hf.lines _ hh

end Lines

section Offender

theorem exists_offender {M O Y E : Subgroup G} (hER : E ≤ normalizer ((Y ⊓ O : Subgroup G) : Set G))
    (hEM : E ≤ M) (hEel : IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hJ : ¬ ∃ E : Subgroup G, E ≤ normalizer ((thompsonJ Y : Subgroup G) : Set G) ⊓ M ∧
      IsElemAbelian 3 E ∧ Nat.card E = 27) :
    ∃ A : Subgroup G, IsMaxElemAbelian Y A ∧ ¬ A ≤ O := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  have hmap : ∀ q ∈ E, (thompsonJ Y).map (MulAut.conj q).toMonoidHom ≤ thompsonJ Y := by
    intro q hq
    have hRq := GL83P3A6Off.map_conj_eq_of_mem_normalizer (hER hq)
    unfold thompsonJ
    rw [Subgroup.map_iSup]
    refine iSup_le fun A => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hA => ?_
    have hAR : A ≤ Y ⊓ O := le_inf hA.1 (hcon A hA)
    have hAq : A.map (MulAut.conj q).toMonoidHom ≤ Y ⊓ O := by
      rw [← hRq]
      exact Subgroup.map_mono hAR
    have hmax : IsMaxElemAbelian Y (A.map (MulAut.conj q).toMonoidHom) := by
      refine ⟨hAq.trans inf_le_left, GL83P3A6Core.isElemAbelian_conj hA.2.1 q, fun B hB hBel => ?_⟩
      rw [Subgroup.card_map_of_injective (MulAut.conj q).injective]
      exact hA.2.2 B hB hBel
    exact le_iSup₂_of_le (A.map (MulAut.conj q).toMonoidHom) hmax le_rfl
  have hEJ : E ≤ normalizer ((thompsonJ Y : Subgroup G) : Set G) := fun q hq =>
    mem_normalizer_of_map_le (hmap q hq)
  exact hJ ⟨E, le_inf hEJ hEM, hEel, hE27⟩

end Offender

section TLevel

variable {M O : Subgroup G} [hn : (O.subgroupOf M).Normal] {x e₂ e₃ t ρ : G} {s : ℤ}
  (hf : A6VIFrame M O x e₂ e₃ t ρ s)

include hf

theorem gen_pow_three {x' : G} (hx'ℓ : x' = x ∨ x' = e₂ ∨ x' = e₃) : x' ^ 3 = 1 ∧ x' ≠ 1 := by
  rcases hx'ℓ with h | h | h <;> rw [h]
  · exact ⟨hf.x_pow, hf.x_ne⟩
  · exact ⟨hf.e₂_pow, hf.e₂_ne⟩
  · exact ⟨hf.e₃_pow, hf.e₃_ne⟩

theorem gen_mem {x' : G} (hx'ℓ : x' = x ∨ x' = e₂ ∨ x' = e₃) : x' ∈ M := by
  rcases hx'ℓ with h | h | h <;> rw [h]
  · exact hf.x_mem
  · exact hf.e₂_mem
  · exact hf.e₃_mem

theorem weak_closure {U : Subgroup G} {x' : G} (hUQ : U ≤ Qf x e₂ e₃)
    (hx'ℓ : x' = x ∨ x' = e₂ ∨ x' = e₃)
    (hedge : ∀ u ∈ U, (u ∈ zpowers x ∨ u ∈ zpowers e₂ ∨ u ∈ zpowers e₃) → u ∈ zpowers x')
    {g : G} (hgM : g ∈ M)
    (hle : (zpowers (QuotientGroup.mk ⟨x', gen_mem hf hx'ℓ⟩ : M ⧸ O.subgroupOf M)).map
        (MulAut.conj (QuotientGroup.mk ⟨g, hgM⟩ : M ⧸ O.subgroupOf M)).toMonoidHom ≤
        img M O U) :
    (zpowers (QuotientGroup.mk ⟨x', gen_mem hf hx'ℓ⟩ : M ⧸ O.subgroupOf M)).map
        (MulAut.conj (QuotientGroup.mk ⟨g, hgM⟩ : M ⧸ O.subgroupOf M)).toMonoidHom =
      zpowers (QuotientGroup.mk ⟨x', gen_mem hf hx'ℓ⟩ : M ⧸ O.subgroupOf M) := by
  have hx'M := gen_mem hf hx'ℓ
  obtain ⟨hx'3, hx'1⟩ := gen_pow_three hf hx'ℓ
  have hyM : g * x' * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM hx'M) (M.inv_mem hgM)
  have hyUq : (QuotientGroup.mk ⟨g * x' * g⁻¹, hyM⟩ : M ⧸ O.subgroupOf M) ∈ img M O U := by
    apply hle
    refine ⟨QuotientGroup.mk ⟨x', hx'M⟩, mem_zpowers _, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  obtain ⟨u, huU, huM, hu⟩ := mem_img_iff.mp hyUq
  have hO : u⁻¹ * (g * x' * g⁻¹) ∈ O := (mk_eq_iff huM hyM).mp hu
  have hy3 : (g * x' * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx'3]; group
  have hy1 : g * x' * g⁻¹ ≠ 1 := by
    intro h1
    apply hx'1
    have : x' = g⁻¹ * (g * x' * g⁻¹) * g := by group
    rw [this, h1]; group
  have hu3 : u ^ 3 = 1 := hf.Q_exp u (hUQ huU)
  have hu1 : u ≠ 1 := by
    intro h1
    rw [h1, inv_one, one_mul] at hO
    have hord : orderOf (g * x' * g⁻¹) = 3 := orderOf_eq_prime hy3 hy1
    have hdvd : orderOf (⟨g * x' * g⁻¹, hO⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hord] at hdvd
    exact hf.O_cop hdvd
  have huord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hU3 : Nat.card (zpowers u) = 3 := by rw [Nat.card_zpowers, huord]
  have huQ : zpowers u ≤ Qf x e₂ e₃ := zpowers_le.mpr (hUQ huU)
  have hUN : zpowers u ≤ normalizer (O : Set G) := huQ.trans hf.Q_le_N
  have hw : g * x' * g⁻¹ ∈ zpowers u ⊔ O := by
    have : g * x' * g⁻¹ = u * (u⁻¹ * (g * x' * g⁻¹)) := by group
    rw [this]
    exact mul_mem_sup (mem_zpowers u) hO
  obtain ⟨k, hk, hkw⟩ := e9r_exists_conj_zpowers_eq hUN hf.O_cop hU3 hw hy3 hy1
  have hkM : k ∈ M := by
    have : zpowers u ⊔ O ≤ M := sup_le ((huQ.trans hf.Q_le_M)) hf.O_le
    exact this hk
  have hwU : k⁻¹ * (g * x' * g⁻¹) * k ∈ zpowers u := by rw [← hkw]; exact mem_zpowers _
  have hwQ : k⁻¹ * (g * x' * g⁻¹) * k ∈ Qf x e₂ e₃ := huQ hwU
  have hwe : k⁻¹ * (g * x' * g⁻¹) * k = (k⁻¹ * g) * x' * (k⁻¹ * g)⁻¹ := by group
  have hline := conj_line hf hx'ℓ (k⁻¹ * g) (hwe ▸ hwQ)
  rw [← hwe] at hline
  have hwx' : k⁻¹ * (g * x' * g⁻¹) * k ∈ zpowers x' := by
    have hwUU : k⁻¹ * (g * x' * g⁻¹) * k ∈ U := by
      have : zpowers u ≤ U := zpowers_le.mpr huU
      exact this hwU
    exact hedge _ hwUU hline
  have hw1 : k⁻¹ * (g * x' * g⁻¹) * k ≠ 1 := by
    intro h1
    apply hy1
    have : g * x' * g⁻¹ = k * (k⁻¹ * (g * x' * g⁻¹) * k) * k⁻¹ := by group
    rw [this, h1]; group
  have hux' : u ∈ zpowers x' := by
    have h1 : zpowers (k⁻¹ * (g * x' * g⁻¹) * k) = zpowers x' :=
      GL83P3A6Aux.zpowers_eq_of_mem hx'3 hx'1 hwx' hw1
    rw [← h1, hkw]
    exact mem_zpowers u
  have hyXq : (QuotientGroup.mk ⟨g * x' * g⁻¹, hyM⟩ : M ⧸ O.subgroupOf M) ∈
      zpowers (QuotientGroup.mk ⟨x', hx'M⟩ : M ⧸ O.subgroupOf M) := by
    rw [← hu]
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hux'
    refine ⟨m, ?_⟩
    show (QuotientGroup.mk ⟨x', hx'M⟩ : M ⧸ O.subgroupOf M) ^ m = QuotientGroup.mk ⟨u, huM⟩
    rw [← QuotientGroup.mk_zpow]
    congr 1
    exact Subtype.ext (by simpa using hm)
  rw [MonoidHom.map_zpowers]
  have hle' : zpowers ((MulAut.conj (QuotientGroup.mk ⟨g, hgM⟩ : M ⧸ O.subgroupOf M)).toMonoidHom
      (QuotientGroup.mk ⟨x', hx'M⟩)) ≤
      zpowers (QuotientGroup.mk ⟨x', hx'M⟩ : M ⧸ O.subgroupOf M) := by
    apply zpowers_le.mpr
    convert hyXq using 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  refine Subgroup.eq_of_le_of_card_ge hle' ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_injective _ (MulAut.conj _).injective]

end TLevel

theorem card_centralizer_conj {T : Type} [Group T] [Finite T] (L : Subgroup T) [hL : L.Normal]
    (a τ : T) :
    Nat.card ↥(L ⊓ centralizer ({τ * a * τ⁻¹} : Set T)) =
      Nat.card ↥(L ⊓ centralizer ({a} : Set T)) := by
  have h : L ⊓ centralizer ({τ * a * τ⁻¹} : Set T) =
      (L ⊓ centralizer ({a} : Set T)).map (MulAut.conj τ).toMonoidHom := by
    ext z
    simp only [mem_inf, mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨hzL, hz⟩
      refine ⟨τ⁻¹ * z * τ, ⟨?_, ?_⟩, by group⟩
      · simpa using hL.conj_mem z hzL τ⁻¹
      · calc τ⁻¹ * z * τ * a = τ⁻¹ * (z * (τ * a * τ⁻¹)) * τ := by group
          _ = τ⁻¹ * ((τ * a * τ⁻¹) * z) * τ := by rw [hz]
          _ = a * (τ⁻¹ * z * τ) := by group
    · rintro ⟨w, ⟨hwL, hw⟩, rfl⟩
      refine ⟨hL.conj_mem w hwL τ, ?_⟩
      calc τ * w * τ⁻¹ * (τ * a * τ⁻¹) = τ * (w * a) * τ⁻¹ := by group
        _ = τ * (a * w) * τ⁻¹ := by rw [hw]
        _ = (τ * a * τ⁻¹) * (τ * w * τ⁻¹) := by group
  rw [h]
  exact Subgroup.card_map_of_injective (MulAut.conj τ).injective

section Lift

variable {M O : Subgroup G} [hn : (O.subgroupOf M).Normal]

theorem exists_lift {R : Subgroup G} (hOM : O ≤ M) (hOn : M ≤ normalizer (O : Set G))
    (hR : IsSylowOf 2 R O) (z : M ⧸ O.subgroupOf M) :
    ∃ γ : G, ∃ hγ : γ ∈ M, γ ∈ normalizer (R : Set G) ∧
      (QuotientGroup.mk ⟨γ, hγ⟩ : M ⧸ O.subgroupOf M) = z := by
  obtain ⟨m, hm, rfl⟩ := exists_mk (M := M) (O := O) z
  obtain ⟨o, ho, h, hh, hmoh⟩ := GL83P3A6Syl.exists_mul_normalizer hR (hOn hm)
  have hhM : h ∈ M := by
    have : h = o⁻¹ * m := by rw [hmoh]; group
    rw [this]
    exact M.mul_mem (M.inv_mem (hOM ho)) hm
  refine ⟨h, hhM, hh, ?_⟩
  rw [mk_eq_iff hhM hm]
  have : h⁻¹ * m = h⁻¹ * o * h := by rw [hmoh]; group
  rw [this]
  have h1 := (mem_normalizer_iff.mp (hOn (M.inv_mem hhM)) o).mp ho
  simpa using h1

theorem x_mem_sup {ι : Type} [Fintype ι] {R A : Subgroup G} (γ : ι → G) (hγM : ∀ i, γ i ∈ M)
    (hγH : ∀ i, γ i ∈ normalizer (R : Set G)) (hAH : A ≤ normalizer (R : Set G))
    (hAM : A ≤ M) {x' : G} (hx'M : x' ∈ M) (hx'N : x' ∈ normalizer (R : Set G))
    (h : (QuotientGroup.mk ⟨x', hx'M⟩ : M ⧸ O.subgroupOf M) ∈
      ⨆ i, (img M O A).map (MulAut.conj (QuotientGroup.mk ⟨γ i, hγM i⟩ :
        M ⧸ O.subgroupOf M)).toMonoidHom) :
    x' ∈ (⨆ i, A.map (MulAut.conj (γ i)).toMonoidHom) ⊔ (O ⊓ (normalizer (R : Set G) ⊓ M)) := by
  set D : Subgroup G := ⨆ i, A.map (MulAut.conj (γ i)).toMonoidHom with hD
  have hsub : (⨆ i, (img M O A).map (MulAut.conj (QuotientGroup.mk ⟨γ i, hγM i⟩ :
      M ⧸ O.subgroupOf M)).toMonoidHom) ≤ img M O D := by
    refine iSup_le fun i => ?_
    rw [← img_conj (hγM i)]
    exact img_mono (le_iSup (fun i => A.map (MulAut.conj (γ i)).toMonoidHom) i)
  obtain ⟨d, hdD, hdM, hd⟩ := mem_img_iff.mp (hsub h)
  have hdO : d⁻¹ * x' ∈ O := (mk_eq_iff hdM hx'M).mp hd
  have hDH : D ≤ normalizer (R : Set G) ⊓ M := by
    refine iSup_le fun i => ?_
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hγ : γ i ∈ normalizer (R : Set G) ⊓ M := ⟨hγH i, hγM i⟩
    have haH : a ∈ normalizer (R : Set G) ⊓ M := ⟨hAH ha, hAM ha⟩
    exact (normalizer (R : Set G) ⊓ M).mul_mem
      ((normalizer (R : Set G) ⊓ M).mul_mem hγ haH) ((normalizer (R : Set G) ⊓ M).inv_mem hγ)
  have hx'H : x' ∈ normalizer (R : Set G) ⊓ M := ⟨hx'N, hx'M⟩
  have hdH := hDH hdD
  have : x' = d * (d⁻¹ * x') := by group
  rw [this]
  exact mul_mem_sup hdD ⟨hdO, (normalizer (R : Set G) ⊓ M).mul_mem
    ((normalizer (R : Set G) ⊓ M).inv_mem hdH) hx'H⟩

end Lift

def LayerOut (M O : Subgroup G) [(O.subgroupOf M).Normal] (Q : Subgroup G) (x : G) (hx : x ∈ M) :
    Prop :=
  ∃ L : Subgroup (M ⧸ O.subgroupOf M), L.Normal ∧ Nonempty (↥L ≃* PSp43) ∧
    centralizer (L : Set (M ⧸ O.subgroupOf M)) = ⊥ ∧ img M O Q ≤ L ∧
    Nat.card ↥(L ⊓ centralizer ({(QuotientGroup.mk ⟨x, hx⟩ : M ⧸ O.subgroupOf M)} :
      Set (M ⧸ O.subgroupOf M))) = 108

structure CoreData (M O : Subgroup G) [(O.subgroupOf M).Normal] (x e₂ e₃ t ρ : G) (s : ℤ)
    (Y U : Subgroup G) (x' : G) : Prop where
  frame : A6VIFrame M O x e₂ e₃ t ρ s
  Y2 : IsPGroup 2 Y
  YM : Y ≤ M
  YO : IsSylowOf 2 (Y ⊓ O) O
  tR : t ∈ normalizer ((Y ⊓ O : Subgroup G) : Set G)
  ρR : ρ ∈ normalizer ((Y ⊓ O : Subgroup G) : Set G)
  QR : Qf x e₂ e₃ ≤ normalizer ((Y ⊓ O : Subgroup G) : Set G)
  UQ : U ≤ Qf x e₂ e₃
  U9 : Nat.card U = 9
  UY : U ≤ normalizer (Y : Set G)
  x'ℓ : x' = x ∨ x' = e₂ ∨ x' = e₃
  x'U : x' ∈ U
  edge : ∀ u ∈ U, (u ∈ zpowers x ∨ u ∈ zpowers e₂ ∨ u ∈ zpowers e₃) → u ∈ zpowers x'
  YN : ¬ Y ≤ normalizer ((Qf x e₂ e₃ ⊔ O : Subgroup G) : Set G)
  A_ex : ∃ A : Subgroup G, IsMaxElemAbelian Y A ∧ ¬ A ≤ O
  odd : ∀ ℓ, (ℓ = x ∨ ℓ = e₂ ∨ ℓ = e₃) → ∀ w ∈ O, w ^ 2 = 1 → w * ℓ = ℓ * w → w = 1

section Main

variable {M O : Subgroup G} [hn : (O.subgroupOf M).Normal] {x e₂ e₃ t ρ : G} {s : ℤ}
  {Y U : Subgroup G} {x' : G} (hd : CoreData M O x e₂ e₃ t ρ s Y U x')

include hd

theorem CoreData.R_ne_bot : (Y ⊓ O : Subgroup G) ≠ ⊥ := by
  have hf := hd.frame
  have hO₂Y : pCoreOf 2 M ≤ Y ⊓ O :=
    e9_le_of_normal hf.O₂_le
      (hf.O_le.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M) hd.YO
  intro hbot
  apply hf.O₂_ne
  rw [eq_bot_iff]
  intro g hg
  have := hO₂Y hg
  rw [hbot] at this
  exact this

theorem CoreData.lower : 256 ≤ Nat.card (Wsub (Y ⊓ O : Subgroup G)) := by
  have hf := hd.frame
  set R : Subgroup G := Y ⊓ O with hR
  have hQM : Qf x e₂ e₃ ≤ M := hf.Q_le_M
  have hnW : ∀ h ∈ normalizer (R : Set G), h ∈ normalizer ((Wsub R : Subgroup G) : Set G) :=
    fun h hh => mem_normalizer_Wsub hh
  have hxQ : x ∈ Qf x e₂ e₃ := mem_sup_left (mem_zpowers x)
  have h2Q : e₂ ∈ Qf x e₂ e₃ := mem_sup_right (mem_sup_left (mem_zpowers e₂))
  have h3Q : e₃ ∈ Qf x e₂ e₃ := mem_sup_right (mem_sup_right (mem_zpowers e₃))
  have hF : GL83P3A6Mod.Frame3 x e₂ e₃ t ρ s :=
    { x3 := hf.x_pow, e₂3 := hf.e₂_pow, e₃3 := hf.e₃_pow, c₂ := hf.comm_x₂, c₃ := hf.comm_x₃,
      c₂₃ := hf.comm_23, tx := hf.t_x, te₂ := hf.t_e₂, te₃ := hf.t_e₃, ρx := hf.ρ_x,
      ρe₂ := hf.ρ_e₂, ρe₃ := hf.ρ_e₃, s_cases := hf.s_cases }
  have hfix : ∀ ℓ, (ℓ = x ∨ ℓ = e₂ ∨ ℓ = e₃) → ∀ w ∈ Wsub R, ℓ * w = w * ℓ → w = 1 :=
    fun ℓ hℓ w hw hcomm =>
      hd.odd ℓ hℓ w (Wsub_le R hw).2 (Wsub_sq hw) hcomm.symm
  exact GL83P3A6Mod.card_ge_of_frame hF (fun w hw => Wsub_sq hw)
    (fun a ha b hb => Wsub_comm ha hb) (hnW _ (hd.QR hxQ)) (hnW _ (hd.QR h2Q))
    (hnW _ (hd.QR h3Q)) (hnW _ hd.tR) (hnW _ hd.ρR)
    (hfix x (Or.inl rfl)) (hfix e₂ (Or.inr (Or.inl rfl))) (hfix e₃ (Or.inr (Or.inr rfl)))
    (Wsub_ne_bot (hd.Y2.to_le inf_le_left) hd.R_ne_bot)

theorem CoreData.upper (h2811 : KFact2811) (hLe8 : KFactPSp43ElemLe8)
    (h2sub : KFactPSp43TwoSubgroups) (hL : LayerOut M O (Qf x e₂ e₃) x hd.frame.x_mem) :
    Nat.card (Wsub (Y ⊓ O : Subgroup G)) ≤ 64 := by
  classical
  have hf := hd.frame
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨L, hLn, hLiso, hLc, hQL, hL108⟩ := hL
  haveI := hLn
  set R : Subgroup G := Y ⊓ O with hR
  have hQM : Qf x e₂ e₃ ≤ M := hf.Q_le_M
  set H₀ : Subgroup G := normalizer (R : Set G) ⊓ M with hH₀
  have hYR : ∀ y ∈ Y, y ∈ normalizer (R : Set G) := by
    intro y hy
    refine mem_normalizer_iff.mpr fun z => ?_
    have h1 := mem_normalizer_iff.mp (Subgroup.le_normalizer hy) z
    have h2 := mem_normalizer_iff.mp (hf.O_norm (hd.YM hy)) z
    rw [hR, mem_inf, mem_inf, ← h1, ← h2]
  have hYH : Y ≤ H₀ := fun y hy => ⟨hYR y hy, hd.YM hy⟩
  have hQH : Qf x e₂ e₃ ≤ H₀ := fun q hq => ⟨hd.QR hq, hQM hq⟩
  have hWH : ∀ h ∈ H₀, h ∈ normalizer ((Wsub R : Subgroup G) : Set G) :=
    fun h hh => mem_normalizer_Wsub hh.1
  set K₀ : Subgroup G := O ⊓ H₀ with hK₀
  have hK₀H : K₀ ≤ H₀ := inf_le_right
  have hK₀n : ∀ h ∈ H₀, ∀ k ∈ K₀, h * k * h⁻¹ ∈ K₀ := fun h hh k hk =>
    ⟨(mem_normalizer_iff.mp (hf.O_norm hh.2) k).mp hk.1,
      H₀.mul_mem (H₀.mul_mem hh hk.2) (H₀.inv_mem hh)⟩
  have hK₀3 : ¬ 3 ∣ Nat.card K₀ := fun h =>
    hf.O_cop (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  obtain ⟨A, hA, hAO⟩ := hd.A_ex
  have hAY : A ≤ Y := hA.1
  have hAM : A ≤ M := hAY.trans hd.YM
  have hAH : A ≤ H₀ := hAY.trans hYH
  have hAK : A ⊓ O ≤ centralizer ((Wsub R : Subgroup G) : Set G) := by
    intro a ha
    refine mem_centralizer_iff.mpr fun w hw => ?_
    exact (Wsub_central hw (show a ∈ R from ⟨hAY ha.1, ha.2⟩)).symm
  have hrel : (centralizer (A : Set G)).relIndex (Wsub R) ≤ (A ⊓ O).relIndex A :=
    GL83P3A6Off.relIndex_le_of_offender hA.2.1 hA.1 hA.2.2 (isElemAbelian_Wsub R)
      ((Wsub_le R).trans inf_le_left) hAK
  have hcardimg : Nat.card (img M O A) = (A ⊓ O).relIndex A := card_img hAM
  have hx'M := gen_mem hf hd.x'ℓ
  obtain ⟨hx'3, hx'1⟩ := gen_pow_three hf hd.x'ℓ
  have hXU := mk_mem_img (O := O) hd.x'U hx'M
  have hXQ := mk_mem_img (O := O) (hd.UQ hd.x'U) hx'M
  have hQ27 : Nat.card (img M O (Qf x e₂ e₃)) = 27 := by
    rw [card_img_of_inf hQM hf.Q_inf_O]
    exact hf.Q_card
  have hUO : U ⊓ O = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have : z ∈ Qf x e₂ e₃ ⊓ O := ⟨hd.UQ hz.1, hz.2⟩
    rw [hf.Q_inf_O] at this
    exact this
  have hU9' : Nat.card (img M O U) = 9 := by
    rw [card_img_of_inf (hd.UQ.trans hQM) hUO]
    exact hd.U9
  have hX108 : Nat.card ↥(L ⊓ centralizer ({(QuotientGroup.mk ⟨x', hx'M⟩ :
      M ⧸ O.subgroupOf M)} : Set (M ⧸ O.subgroupOf M))) = 108 := by
    have e2 : (QuotientGroup.mk ⟨e₂, hf.e₂_mem⟩ : M ⧸ O.subgroupOf M) =
        QuotientGroup.mk ⟨t, hf.t_mem⟩ * QuotientGroup.mk ⟨x, hf.x_mem⟩ *
          (QuotientGroup.mk ⟨t, hf.t_mem⟩)⁻¹ := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hf.t_x.symm
    have e3 : (QuotientGroup.mk ⟨e₃, hf.e₃_mem⟩ : M ⧸ O.subgroupOf M) =
        QuotientGroup.mk ⟨t, hf.t_mem⟩ * QuotientGroup.mk ⟨e₂, hf.e₂_mem⟩ *
          (QuotientGroup.mk ⟨t, hf.t_mem⟩)⁻¹ := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hf.t_e₂.symm
    rcases hd.x'ℓ with h | h | h
    · have : (⟨x', hx'M⟩ : M) = ⟨x, hf.x_mem⟩ := Subtype.ext h
      rw [this]
      exact hL108
    · have : (⟨x', hx'M⟩ : M) = ⟨e₂, hf.e₂_mem⟩ := Subtype.ext h
      rw [this, e2, card_centralizer_conj]
      exact hL108
    · have : (⟨x', hx'M⟩ : M) = ⟨e₃, hf.e₃_mem⟩ := Subtype.ext h
      rw [this, e3, card_centralizer_conj, e2, card_centralizer_conj]
      exact hL108
  have hwc : ∀ g ∈ L, (zpowers (QuotientGroup.mk ⟨x', hx'M⟩ : M ⧸ O.subgroupOf M)).map
      (MulAut.conj g).toMonoidHom ≤ img M O U →
      (zpowers (QuotientGroup.mk ⟨x', hx'M⟩ : M ⧸ O.subgroupOf M)).map
        (MulAut.conj g).toMonoidHom = zpowers (QuotientGroup.mk ⟨x', hx'M⟩ :
          M ⧸ O.subgroupOf M) := by
    intro g _ hle
    obtain ⟨γ, hγM, rfl⟩ := exists_mk (M := M) (O := O) g
    exact weak_closure hf hd.UQ hd.x'ℓ hd.edge hγM hle
  have hdich := h2sub (M ⧸ O.subgroupOf M) L hLn hLiso hLc (img M O (Qf x e₂ e₃)) (img M O U)
    (QuotientGroup.mk ⟨x', hx'M⟩) hQL (isElemAbelian_img hf.Q_el) hQ27 (img_mono hd.UQ) hU9'
    hXU (hQL hXQ) hX108 hwc (img M O Y) (isPGroup_img hd.Y2) (img_le_normalizer hd.UY)
  rcases hdich with hnorm | ⟨z, hzL, hz2, hz1, hz576, hYz⟩
  · exfalso
    apply hd.YN
    intro y hy
    have hyM : y ∈ M := hd.YM hy
    apply mem_normalizer_of_map_le
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hqM : q ∈ M := hQM hq
      have hyqM : y * q * y⁻¹ ∈ M := M.mul_mem (M.mul_mem hyM hqM) (M.inv_mem hyM)
      have hmem := (mem_normalizer_iff.mp (hnorm (mk_mem_img hy hyM))
        (QuotientGroup.mk ⟨q, hqM⟩)).mp (mk_mem_img hq hqM)
      have e : (QuotientGroup.mk ⟨y, hyM⟩ : M ⧸ O.subgroupOf M) * QuotientGroup.mk ⟨q, hqM⟩ *
          (QuotientGroup.mk ⟨y, hyM⟩)⁻¹ = QuotientGroup.mk ⟨y * q * y⁻¹, hyqM⟩ := by
        rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        rfl
      rw [e] at hmem
      obtain ⟨q', hq'Q, hq'M, hq'⟩ := mem_img_iff.mp hmem
      have h1 := (mk_eq_iff hq'M hyqM).mp hq'
      have h3 : y * q * y⁻¹ = q' * (q'⁻¹ * (y * q * y⁻¹)) := by group
      rw [h3]
      exact mul_mem_sup hq'Q h1
    · rintro _ ⟨o, ho, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mem_sup_right ((mem_normalizer_iff.mp (hf.O_norm hyM) o).mp ho)
  · have hĀle : img M O A ≤ pCoreOf 2 (L ⊓ centralizer ({z} : Set (M ⧸ O.subgroupOf M))) :=
      (img_mono hAY).trans hYz
    have hĀel : IsElemAbelian 2 (img M O A) := isElemAbelian_img hA.2.1
    have hĀne : img M O A ≠ ⊥ := by
      intro hbot
      apply hAO
      intro a ha
      have haM : a ∈ M := hAM ha
      have h1 : (QuotientGroup.mk ⟨a, haM⟩ : M ⧸ O.subgroupOf M) ∈ img M O A :=
        mk_mem_img ha haM
      rw [hbot, mem_bot] at h1
      exact (mk_eq_one_iff haM).mp h1
    have hX3 : (QuotientGroup.mk ⟨x', hx'M⟩ : M ⧸ O.subgroupOf M) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : (⟨x', hx'M⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hx'3)
      rw [this]
      rfl
    obtain ⟨hk2, hk4⟩ := h2811 (M ⧸ O.subgroupOf M) L hLiso z hzL hz2 hz1 hz576
      (QuotientGroup.mk ⟨x', hx'M⟩) (hQL hXQ) hX3 hX108 (img M O A) hĀne hĀel hĀle
    have hb8 := hLe8 (M ⧸ O.subgroupOf M) L hLiso z hzL hz2 hz1 hz576 (img M O A) hĀel hĀle
    have hx'N : x' ∈ normalizer (R : Set G) := hd.QR (hd.UQ hd.x'U)
    have hx'H : x' ∈ H₀ := hQH (hd.UQ hd.x'U)
    have hlift : ∀ w : M ⧸ O.subgroupOf M, ∃ γ : G, ∃ hγ : γ ∈ M, γ ∈ normalizer (R : Set G) ∧
        (QuotientGroup.mk ⟨γ, hγ⟩ : M ⧸ O.subgroupOf M) = w := exists_lift hf.O_le hf.O_norm hd.YO
    choose γ hγM hγN hγ using hlift
    have hbound : ∀ (ι : Type) [Fintype ι] (g : ι → M ⧸ O.subgroupOf M) (b : ℕ),
        Nat.card (img M O A) ≤ b →
        (QuotientGroup.mk ⟨x', hx'M⟩ : M ⧸ O.subgroupOf M) ∈
          ⨆ i, (img M O A).map (MulAut.conj (g i)).toMonoidHom →
        Nat.card (Wsub R) ≤ b ^ Fintype.card ι := by
      intro ι _ g b hb hmem
      have hγH : ∀ i, γ (g i) ∈ H₀ := fun i => ⟨hγN (g i), hγM (g i)⟩
      refine GL83P3A6Off.card_le_pow (H := H₀) (K := K₀) (W := Wsub R)
        (fun i => A.map (MulAut.conj (γ (g i))).toMonoidHom) b hK₀H hK₀n hK₀3 hWH
        (fun i => ?_) (fun i => ?_) hx'H hx'3 ?_ (fun w hw hcomm =>
          hd.odd x' hd.x'ℓ w (Wsub_le R hw).2 (Wsub_sq hw) hcomm.symm)
      · rintro _ ⟨a, ha, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact H₀.mul_mem (H₀.mul_mem (hγH i) (hAH ha)) (H₀.inv_mem (hγH i))
      · have h1 := GL83P3A6Off.relIndex_centralizer_conj (A := A) (W := Wsub R)
          (hWH _ (hγH i))
        rw [h1]
        refine hrel.trans ?_
        rw [← hcardimg]
        exact hb
      · refine x_mem_sup (fun i => γ (g i)) (fun i => hγM (g i)) (fun i => hγN (g i))
          (hAY.trans (fun y hy => hYR y hy)) hAM hx'M hx'N ?_
        simpa only [hγ] using hmem
    by_cases hAz : img M O A ≤ zpowers z
    · obtain ⟨g, hgL, hxg⟩ := hk4
      have hb2 : Nat.card (img M O A) ≤ 2 := by
        have h1 := Subgroup.card_le_of_le hAz
        rwa [Nat.card_zpowers, orderOf_eq_prime hz2 hz1] at h1
      have h1 := hbound (Fin 4) g 2 hb2 hxg
      rw [Fintype.card_fin] at h1
      exact h1.trans (by norm_num)
    · obtain ⟨g₁, hg₁, g₂, hg₂, hxg⟩ := hk2 hAz
      have hxg' : (QuotientGroup.mk ⟨x', hx'M⟩ : M ⧸ O.subgroupOf M) ∈
          ⨆ b : Bool, (img M O A).map
            (MulAut.conj (cond b g₁ g₂)).toMonoidHom := by
        rw [iSup_bool_eq]
        exact hxg
      have h1 := hbound Bool (fun b => cond b g₁ g₂) 8 hb8 hxg'
      rw [Fintype.card_bool] at h1
      exact h1.trans (by norm_num)

theorem CoreData.false (h2811 : KFact2811) (hLe8 : KFactPSp43ElemLe8)
    (h2sub : KFactPSp43TwoSubgroups) (hL : LayerOut M O (Qf x e₂ e₃) x hd.frame.x_mem) :
    False := by
  have h1 := hd.lower
  have h2 := hd.upper h2811 hLe8 h2sub hL
  omega

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Core
