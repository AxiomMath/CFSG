module

public import CFSG.LocalAnalysis.GH72.Coprime
public import CFSG.LocalAnalysis.GH72.Sec4Basic
import CFSG.GroupTheory.OddInversion

public section

namespace CFSG.GH72

open Subgroup
open scoped commutatorElement Pointwise MatrixGroups

variable {G : Type} [Group G]

theorem commutator_zpowers_le_of_mem_normalizer {E : Subgroup G} {t : G}
    (htE : t ∈ normalizer (E : Set G)) : ⁅E, zpowers t⁆ ≤ E := by
  rw [commutator_le]
  intro e he s hs
  have hsE : s ∈ normalizer (E : Set G) := (zpowers_le.mpr htE) hs
  have h1 : s * e⁻¹ * s⁻¹ ∈ E := (mem_normalizer_iff.mp hsE e⁻¹).mp (inv_mem he)
  have h2 : ⁅e, s⁆ = e * (s * e⁻¹ * s⁻¹) := by rw [commutatorElement_def]; group
  rw [h2]
  exact mul_mem he h1

theorem commutator_le_left_of_le_normalizer {H K : Subgroup G} (hK : K ≤ normalizer (H : Set G)) :
    ⁅H, K⁆ ≤ H := by
  rw [commutator_le]
  intro h hh k hk
  have h1 : k * h⁻¹ * k⁻¹ ∈ H := (mem_normalizer_iff.mp (hK hk) h⁻¹).mp (inv_mem hh)
  have h2 : ⁅h, k⁆ = h * (k * h⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
  rw [h2]
  exact mul_mem hh h1

theorem mem_normalizer_commutator {H K : Subgroup G} {g : G} (hH : g ∈ normalizer (H : Set G))
    (hK : g ∈ normalizer (K : Set G)) : g ∈ normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [map_commutator, hH, hK]

theorem conj_commutatorElement_eq_inv {t : G} (ht : orderOf t = 2) (e : G) :
    t * ⁅e, t⁆ * t⁻¹ = ⁅e, t⁆⁻¹ := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hti : t⁻¹ = t := OddInversion.inv_eq_self_of_orderOf_eq_two ht
  have key : (e * t * e⁻¹ * t) * (t * e * t * e⁻¹) = 1 := by
    calc (e * t * e⁻¹ * t) * (t * e * t * e⁻¹) = e * t * e⁻¹ * (t * t) * e * t * e⁻¹ := by group
      _ = e * t * e⁻¹ * e * t * e⁻¹ := by rw [htt, mul_one]
      _ = e * (t * t) * e⁻¹ := by group
      _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
  rw [commutatorElement_def, hti]
  calc t * (e * t * e⁻¹ * t) * t = t * e * t * e⁻¹ * (t * t) := by group
    _ = t * e * t * e⁻¹ := by rw [htt, mul_one]
    _ = (e * t * e⁻¹ * t)⁻¹ := (inv_eq_of_mul_eq_one_right key).symm

section Inv

variable {E : Subgroup G} (hE : Odd (Nat.card E)) {t : G} (ht : orderOf t = 2)
  (htE : t ∈ normalizer (E : Set G))
include hE ht htE

theorem commutator_commutator_zpowers_eq : ⁅⁅E, zpowers t⁆, zpowers t⁆ = ⁅E, zpowers t⁆ := by
  have hle := commutator_zpowers_le_of_mem_normalizer htE
  have htK : t ∈ normalizer ((⁅E, zpowers t⁆ : Subgroup G) : Set G) :=
    mem_normalizer_commutator_zpowers htE rfl
  refine le_antisymm (commutator_zpowers_le_of_mem_normalizer htK) ?_
  rw [commutator_le]
  intro e he s hs
  rcases eq_one_or_eq_of_mem_zpowers ht hs with rfl | rfl
  · rw [commutatorElement_one_right]
    exact one_mem _
  · exact mem_commutator_zpowers_of_conj_eq_inv (hE.of_dvd_nat (card_dvd_of_le hle))
      (commutator_mem_commutator he (mem_zpowers _)) (conj_commutatorElement_eq_inv ht e)

theorem commutator_zpowers_eq_bot_of_le {E₀ : Subgroup G} (hEt : ⁅E, zpowers t⁆ ≤ E₀)
    (hE₀t : E₀ ≤ C t) : ⁅E, zpowers t⁆ = ⊥ := by
  rw [← commutator_commutator_zpowers_eq hE ht htE, eq_bot_iff]
  refine (commutator_mono hEt le_rfl).trans (le_of_eq ?_)
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer, zpowers_le, mem_centralizer_iff]
  intro h hh
  exact mem_centralizer_singleton_iff.mp (hE₀t hh)

theorem inf_C_sup_commutator_zpowers_eq : E ⊓ C t ⊔ ⁅E, zpowers t⁆ = E := by
  refine le_antisymm (sup_le inf_le_left (commutator_zpowers_le_of_mem_normalizer htE)) ?_
  intro g hg
  obtain ⟨⟨c, j⟩, ⟨hc, hj⟩, hcj⟩ :=
    (OddInversion.odd_involution_product_decomposition hE ht htE).1.surjOn hg
  simp only at hcj
  rw [← hcj]
  exact mul_mem (le_sup_left (b := ⁅E, zpowers t⁆) hc)
    (le_sup_right (a := E ⊓ C t) (mem_commutator_zpowers_of_conj_eq_inv hE hj.1 hj.2))

omit ht htE in
theorem inf_C_C_sup_commutator_eq {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxy : x * y = y * x) (hxE : x ∈ normalizer (E : Set G)) (hyE : y ∈ normalizer (E : Set G)) :
    E ⊓ C x ⊓ C y ⊔ (⁅E, zpowers x⁆ ⊔ ⁅E, zpowers y⁆) = E := by
  have hyC : y ∈ normalizer ((E ⊓ C x : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hyE, mem_normalizer_C_of_commute hxy.symm⟩
  have h1 := inf_C_sup_commutator_zpowers_eq hE hx hxE
  have h2 := inf_C_sup_commutator_zpowers_eq (hE.of_dvd_nat (card_dvd_of_le inf_le_left)) hy hyC
  refine le_antisymm (sup_le (inf_le_left.trans inf_le_left)
    (sup_le (commutator_zpowers_le_of_mem_normalizer hxE)
      (commutator_zpowers_le_of_mem_normalizer hyE))) ?_
  calc E = E ⊓ C x ⊔ ⁅E, zpowers x⁆ := h1.symm
    _ = E ⊓ C x ⊓ C y ⊔ ⁅E ⊓ C x, zpowers y⁆ ⊔ ⁅E, zpowers x⁆ := by rw [h2]
    _ ≤ E ⊓ C x ⊓ C y ⊔ (⁅E, zpowers x⁆ ⊔ ⁅E, zpowers y⁆) :=
      sup_le (sup_le le_sup_left (le_sup_right.trans' (le_sup_right.trans'
        (commutator_mono inf_le_left le_rfl)))) (le_sup_right.trans' le_sup_left)

omit ht htE in
theorem commute_of_conj_eq_inv_of_le_C {E₀ : Subgroup G} (hEE₀ : E ≤ normalizer (E₀ : Set G))
    {y : G} (hE₀y : E₀ ≤ C y) {j : G} (hjE : j ∈ E) (hj : y * j * y⁻¹ = j⁻¹) {e₀ : G}
    (he₀ : e₀ ∈ E₀) : j * e₀ = e₀ * j := by
  have hc : j * e₀ * j⁻¹ ∈ E₀ := (mem_normalizer_iff.mp (hEE₀ hjE) e₀).mp he₀
  have hfix : ∀ g ∈ E₀, y * g * y⁻¹ = g := fun g hg => by
    rw [← mem_centralizer_singleton_iff.mp (hE₀y hg), mul_inv_cancel_right]
  have h1 : y * (j * e₀ * j⁻¹) * y⁻¹ = j⁻¹ * e₀ * j := by
    calc y * (j * e₀ * j⁻¹) * y⁻¹ = (y * j * y⁻¹) * (y * e₀ * y⁻¹) * (y * j * y⁻¹)⁻¹ := by group
      _ = j⁻¹ * e₀ * j := by rw [hj, hfix e₀ he₀, inv_inv]
  rw [hfix _ hc] at h1
  have hsq : Commute (j ^ 2) e₀ := by
    change j ^ 2 * e₀ = e₀ * j ^ 2
    rw [sq]
    calc j * j * e₀ = j * (j * e₀ * j⁻¹) * j := by group
      _ = j * (j⁻¹ * e₀ * j) * j := by rw [h1]
      _ = e₀ * (j * j) := by group
  have hj2 : (j ^ 2) ^ ((Nat.card E + 1) / 2) = j := by
    rw [← pow_mul, mul_comm, pow_mul, OddInversion.pow_two_mul_eq_self hE hjE]
  have := hsq.pow_left ((Nat.card E + 1) / 2)
  rw [hj2] at this
  exact this

omit ht htE in
theorem eq_bot_and_isCyclic_of_commutator_le {E₀ : Subgroup G} (hE₀E : E₀ ≤ E)
    (hEE₀ : E ≤ normalizer (E₀ : Set G)) {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxE : x ∈ normalizer (E : Set G)) (hyE : y ∈ normalizer (E : Set G)) (hE₀x : E₀ ≤ C x)
    (hE₀y : E₀ ≤ C y) (hEx : ⁅E, zpowers x⁆ ≤ E₀)
    (hEXY : ⁅E, zpowers x⁆ ⊔ ⁅E, zpowers y⁆ = E) {e : G} (he : e ∈ E)
    (hcyc : E ≤ E₀ ⊔ zpowers e) :
    E₀ = ⊥ ∧ IsCyclic E ∧ E ⊓ C y = ⊥ := by
  have hx1 : ⁅E, zpowers x⁆ = ⊥ := commutator_zpowers_eq_bot_of_le hE hx hxE hEx hE₀x
  have hEy : ⁅E, zpowers y⁆ = E := by
    have h := hEXY
    rwa [hx1, bot_sup_eq] at h
  have hle : ⁅E, zpowers y⁆ ≤ centralizer (E₀ : Set G) := by
    rw [commutator_le]
    intro g hg s hs
    rcases eq_one_or_eq_of_mem_zpowers hy hs with rfl | rfl
    · rw [commutatorElement_one_right]
      exact one_mem _
    · rw [mem_centralizer_iff]
      intro e₀ he₀
      exact (commute_of_conj_eq_inv_of_le_C hE hEE₀ hE₀y
        (commutator_zpowers_le_of_mem_normalizer hyE
          (commutator_mem_commutator hg (mem_zpowers _)))
        (conj_commutatorElement_eq_inv hy g) he₀).symm
  have hcomm : ∀ g ∈ E, ∀ e₀ ∈ E₀, g * e₀ = e₀ * g := fun g hg e₀ he₀ =>
    ((mem_centralizer_iff.mp (hle (hEy.symm ▸ hg))) e₀ he₀).symm
  have hset : ((E₀ ⊔ zpowers e : Subgroup G) : Set G) = (E₀ : Set G) * (zpowers e : Set G) :=
    coe_mul_of_right_le_normalizer_left E₀ (zpowers e) (zpowers_le.mpr (hEE₀ he))
  have hzE : zpowers e ≤ E := zpowers_le.mpr he
  have hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have ha' : a ∈ ((E₀ ⊔ zpowers e : Subgroup G) : Set G) := hcyc ha
    have hb' : b ∈ ((E₀ ⊔ zpowers e : Subgroup G) : Set G) := hcyc hb
    rw [hset] at ha' hb'
    obtain ⟨a₀, ha₀, a₁, ha₁, rfl⟩ := Set.mem_mul.mp ha'
    obtain ⟨b₀, hb₀, b₁, hb₁, rfl⟩ := Set.mem_mul.mp hb'
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha₁
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb₁
    have c1 : Commute a₀ b₀ := (hcomm b₀ (hE₀E hb₀) a₀ ha₀).symm
    have c2 : Commute a₀ (e ^ k) := (hcomm _ (hzE (zpow_mem (mem_zpowers e) k)) a₀ ha₀).symm
    have c3 : Commute (e ^ i) b₀ := hcomm _ (hzE (zpow_mem (mem_zpowers e) i)) b₀ hb₀
    have c4 : Commute (e ^ i) (e ^ k) := Commute.zpow_zpow_self e i k
    exact ((c1.mul_right c2).mul_left (c3.mul_right c4)).eq
  have hCy : E ⊓ C y = ⊥ := by
    have h := inf_centralizer_inf_commutator_zpowers hab hE hy hyE
    rw [hEy] at h
    exact eq_bot_iff.mpr ((le_inf le_rfl inf_le_left).trans h.le)
  have hE₀ : E₀ = ⊥ := eq_bot_iff.mpr (hCy ▸ le_inf hE₀E hE₀y)
  refine ⟨hE₀, ?_, hCy⟩
  have hEz : E = zpowers e := le_antisymm (by simpa [hE₀] using hcyc) hzE
  rw [hEz]
  infer_instance

end Inv

theorem O_le (H : Subgroup G) : O H ≤ H := map_subtype_le _

section Bar

variable {H : Subgroup G}

theorem mem_O_iff_mem_oddCore {g : G} (hg : g ∈ H) :
    g ∈ O H ↔ (⟨g, hg⟩ : H) ∈ CFSG.oddCore H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact hh
  · intro h
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem mk_eq_one_iff_mem_O (g : H) : (QuotientGroup.mk g : Bar H) = 1 ↔ (g : G) ∈ O H := by
  rw [QuotientGroup.eq_one_iff, mem_O_iff_mem_oddCore g.2]

theorem mem_bar_iff {K : Subgroup G} {x : Bar H} :
    x ∈ bar H K ↔ ∃ k : H, (k : G) ∈ K ∧ (QuotientGroup.mk k : Bar H) = x := by
  simp only [bar, mem_map, mem_subgroupOf, QuotientGroup.mk'_apply]

theorem bar_commutator {K L : Subgroup G} (hK : K ≤ H) (hL : L ≤ H) :
    bar H ⁅K, L⁆ = ⁅bar H K, bar H L⁆ := by
  have h : ⁅K, L⁆.subgroupOf H = ⁅K.subgroupOf H, L.subgroupOf H⁆ := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (commutator_le_of_le hK hL), map_commutator,
      map_subgroupOf_eq_of_le hK, map_subgroupOf_eq_of_le hL]
  simp only [bar, h, map_commutator]

theorem bar_normal {K : Subgroup G} (hK : (K.subgroupOf H).Normal) : (bar H K).Normal :=
  hK.map _ (QuotientGroup.mk'_surjective _)

theorem card_bar_dvd {K : Subgroup G} (hK : K ≤ H) : Nat.card (bar H K) ∣ Nat.card K := by
  have h := card_map_dvd (H := K.subgroupOf H) (QuotientGroup.mk' (CFSG.oddCore H))
  rwa [Nat.card_congr (subgroupOfEquivOfLe hK).toEquiv] at h

theorem IsPGroup.bar {p : ℕ} {K : Subgroup G} (hK : IsPGroup p K) (hKH : K ≤ H) :
    IsPGroup p (bar H K) :=
  (hK.of_equiv (subgroupOfEquivOfLe hKH).symm).map _

theorem bar_sup_O {K : Subgroup G} (hK : K ≤ H) : bar H (K ⊔ O H) = bar H K := by
  refine le_antisymm ?_ (map_mono fun _ hx => (le_sup_left : K ≤ K ⊔ O H) hx)
  intro x hx
  obtain ⟨g, hg, rfl⟩ := mem_bar_iff.mp hx
  have hg' : (g : G) ∈ ((K ⊔ O H : Subgroup G) : Set G) := hg
  rw [coe_mul_of_left_le_normalizer_right K (O H) (hK.trans (le_normalizer_O H))] at hg'
  obtain ⟨k, hk, o, ho, hko⟩ := Set.mem_mul.mp hg'
  refine mem_bar_iff.mpr ⟨⟨k, hK hk⟩, hk, ?_⟩
  have hoH : o ∈ H := O_le H ho
  have e : g = ⟨k, hK hk⟩ * ⟨o, hoH⟩ := Subtype.ext hko.symm
  rw [e, QuotientGroup.mk_mul, (mk_eq_one_iff_mem_O ⟨o, hoH⟩).mpr ho, mul_one]

theorem bar_le_normalizer {K L : Subgroup G} (hLK : L ≤ normalizer (K : Set G)) :
    bar H L ≤ normalizer (bar H K : Set (Bar H)) := by
  intro x hx
  obtain ⟨l, hl, rfl⟩ := mem_bar_iff.mp hx
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨k, hk, rfl⟩ := mem_bar_iff.mp hy
    refine mem_bar_iff.mpr ⟨l * k * l⁻¹, ?_, by rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv]⟩
    exact (mem_normalizer_iff.mp (hLK hl) k).mp hk
  · intro hy
    obtain ⟨k, hk, hk'⟩ := mem_bar_iff.mp hy
    refine mem_bar_iff.mpr ⟨l⁻¹ * k * l, ?_, ?_⟩
    · have := (mem_normalizer_iff.mp (inv_mem (hLK hl)) k).mp hk
      simpa using this
    · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hk']
      group

theorem exists_le_inf_O_sup_zpowers_of_isCyclic_bar {K : Subgroup G} (hK : K ≤ H)
    (hc : IsCyclic (bar H K)) : ∃ e ∈ K, K ≤ (K ⊓ O H) ⊔ zpowers e := by
  obtain ⟨g, hg⟩ := hc.exists_generator
  obtain ⟨e, heK, hge⟩ := mem_bar_iff.mp g.2
  refine ⟨e, heK, fun k hk => ?_⟩
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp
    (hg ⟨QuotientGroup.mk ⟨k, hK hk⟩, mem_bar_iff.mpr ⟨_, hk, rfl⟩⟩)
  have hn' : (QuotientGroup.mk (e ^ n) : Bar H) = QuotientGroup.mk ⟨k, hK hk⟩ := by
    have h := congrArg Subtype.val hn
    rw [SubgroupClass.coe_zpow, ← hge] at h
    rw [QuotientGroup.mk_zpow]
    exact h
  have h1 : (QuotientGroup.mk ((e ^ n)⁻¹ * ⟨k, hK hk⟩) : Bar H) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hn', inv_mul_cancel]
  rw [mk_eq_one_iff_mem_O] at h1
  have h2 : ((e : G) ^ n)⁻¹ * k ∈ K ⊓ O H :=
    mem_inf.mpr ⟨mul_mem (inv_mem (zpow_mem heK n)) hk, by simpa using h1⟩
  have e3 : k = (e : G) ^ n * (((e : G) ^ n)⁻¹ * k) := by group
  rw [e3]
  exact mul_mem (mem_sup_right (zpow_mem (mem_zpowers _) n)) (mem_sup_left h2)

theorem le_O_of_le_normalizer_of_odd {N : Subgroup G} (hNH : N ≤ H)
    (hHN : H ≤ normalizer (N : Set G)) (hodd : Odd (Nat.card N)) : N ≤ O H := by
  have hn : (N.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  have hodd' : Odd (Nat.card (N.subgroupOf H)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hNH).toEquiv]
  have hle : N.subgroupOf H ≤ CFSG.oddCore H := le_sSup ⟨hn, hodd'⟩
  intro n hn'
  exact ⟨⟨n, hNH hn'⟩, hle hn', rfl⟩

theorem isKleinFour_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [IsKleinFour X] (e : X ≃* Y) :
    IsKleinFour Y :=
  ⟨by rw [← Nat.card_congr e.toEquiv]; exact IsKleinFour.card_four,
    by rw [← Monoid.exponent_eq_of_mulEquiv e]; exact IsKleinFour.exponent_two⟩

theorem isKleinFour_bar {V : Subgroup G} (hV : IsKleinFour V) (hVH : V ≤ H) (hVO : V ⊓ O H = ⊥) :
    IsKleinFour (bar H V) := by
  let ψ : V →* Bar H := (QuotientGroup.mk' (CFSG.oddCore H)).comp (inclusion hVH)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro v hv
    rw [MonoidHom.mem_ker] at hv
    change (QuotientGroup.mk (inclusion hVH v) : Bar H) = 1 at hv
    rw [mk_eq_one_iff_mem_O] at hv
    have hv' : (v : G) ∈ V ⊓ O H := ⟨v.2, hv⟩
    rw [hVO, mem_bot] at hv'
    exact (mem_bot).mpr (Subtype.ext hv')
  have hr : ψ.range = bar H V := by
    ext x
    rw [MonoidHom.mem_range, mem_bar_iff]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨inclusion hVH v, v.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  exact isKleinFour_of_mulEquiv ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hr))

theorem quotIs_bar_inf {N₀ Ō W : Subgroup G} (hle : Ō ≤ N₀) (hn : N₀ ≤ normalizer (Ō : Set G))
    (hWH : W ≤ H) (hWN : W ≤ N₀) (hcov : Covers W N₀ Ō) (hker : O H ⊓ W = W ⊓ Ō)
    {P : ∀ L : Type, Group L → Prop} (hq : QuotIs N₀ Ō P) :
    ∃ (L : Type) (_ : Group L), Nonempty (bar H W ≃* L) ∧ P L inferInstance := by
  obtain ⟨L, _, f, hf, hfker, hP⟩ := hq
  refine ⟨L, inferInstance, ?_, hP⟩
  let ψ : ↥W →* Bar H := (QuotientGroup.mk' (CFSG.oddCore H)).comp (inclusion hWH)
  let φ : ↥W →* L := f.comp (inclusion hWN)
  have hψr : ψ.range = bar H W := by
    ext x
    rw [MonoidHom.mem_range, mem_bar_iff]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨inclusion hWH k, k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  have hφs : Function.Surjective φ := by
    intro l
    obtain ⟨n, rfl⟩ := hf l
    have hn' : (n : G) ∈ ((W ⊓ N₀ ⊔ Ō : Subgroup G) : Set G) := hcov n.2
    rw [coe_mul_of_left_le_normalizer_right (W ⊓ N₀) Ō (inf_le_right.trans hn)] at hn'
    obtain ⟨k, hk, o, ho, hko⟩ := Set.mem_mul.mp hn'
    refine ⟨⟨k, hk.1⟩, ?_⟩
    have hoN : o ∈ N₀ := hle ho
    have hfo : f ⟨o, hoN⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hfker]
      exact ho
    have e : n = inclusion hWN ⟨k, hk.1⟩ * ⟨o, hoN⟩ := Subtype.ext hko.symm
    change f (inclusion hWN ⟨k, hk.1⟩) = f n
    rw [e, map_mul, hfo, mul_one]
  have hker' : ψ.ker = φ.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change (QuotientGroup.mk (inclusion hWH k) : Bar H) = 1 ↔ f (inclusion hWN k) = 1
    rw [mk_eq_one_iff_mem_O, ← MonoidHom.mem_ker, hfker, mem_subgroupOf]
    change (k : G) ∈ O H ↔ (k : G) ∈ Ō
    constructor
    · intro h
      have h' : (k : G) ∈ O H ⊓ W := ⟨h, k.2⟩
      rw [hker] at h'
      exact h'.2
    · intro h
      have h' : (k : G) ∈ W ⊓ Ō := ⟨k.2, h⟩
      rw [← hker] at h'
      exact h'.1
  exact ⟨(MulEquiv.subgroupCongr hψr.symm).trans ((QuotientGroup.quotientKerEquivRange ψ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker').trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)))⟩

theorem card_bar_eq_card_map {N₀ Ō W : Subgroup G} {L : Type*} [Group L] (f : N₀ →* L)
    (hfker : f.ker = Ō.subgroupOf N₀) (hWH : W ≤ H) (hWN : W ≤ N₀) (hker : O H ⊓ W = W ⊓ Ō)
    {Z : Subgroup G} (hZ : Z ≤ W) : Nat.card (bar H Z) = Nat.card ((Z.subgroupOf N₀).map f) := by
  have hZH : Z ≤ H := hZ.trans hWH
  have hZN : Z ≤ N₀ := hZ.trans hWN
  have h1 : Nat.card (bar H Z) = (O H).relIndex Z := by
    change Nat.card ((Z.subgroupOf H).map (QuotientGroup.mk' (CFSG.oddCore H))) = _
    rw [← relIndex_ker, QuotientGroup.ker_mk']
    have : CFSG.oddCore H = (O H).subgroupOf H :=
      (comap_map_eq_self_of_injective H.subtype_injective _).symm
    rw [this, relIndex_subgroupOf hZH]
  have h2 : Nat.card ((Z.subgroupOf N₀).map f) = Ō.relIndex Z := by
    rw [← relIndex_ker, hfker, relIndex_subgroupOf hZN]
  rw [h1, h2, ← inf_relIndex_right, ← inf_relIndex_right (H := Ō)]
  congr 1
  calc O H ⊓ Z = O H ⊓ W ⊓ Z := by rw [inf_assoc, inf_of_le_right hZ]
    _ = W ⊓ Ō ⊓ Z := by rw [hker]
    _ = Ō ⊓ Z := by rw [inf_comm W, inf_assoc, inf_of_le_right hZ]

theorem card_bar_of_inf_O_eq_bot {K : Subgroup G} (hK : K ≤ H) (h : K ⊓ O H = ⊥) :
    Nat.card (bar H K) = Nat.card K := by
  change Nat.card ((K.subgroupOf H).map (QuotientGroup.mk' (CFSG.oddCore H))) = _
  rw [← relIndex_ker, QuotientGroup.ker_mk']
  have : CFSG.oddCore H = (O H).subgroupOf H :=
    (comap_map_eq_self_of_injective H.subtype_injective _).symm
  rw [this, relIndex_subgroupOf hK, ← inf_relIndex_right, inf_comm, h, relIndex_bot_left]

end Bar

theorem IsL2OrA7.of_mulEquiv {L L' : Type*} [Group L] [Group L'] {q : ℕ} (h : IsL2OrA7 L q)
    (e : L ≃* L') : IsL2OrA7 L' q := by
  rcases h with hf | ⟨r, k, hr, hr2, hq, hf⟩
  · obtain ⟨f⟩ := hf
    exact Or.inl ⟨e.symm.trans f⟩
  · obtain ⟨f⟩ := hf
    exact Or.inr ⟨r, k, hr, hr2, hq, ⟨e.symm.trans f⟩⟩

theorem IsL2OrA7.mono {L : Type*} [Group L] {q q' : ℕ} (h : IsL2OrA7 L q) (hqq : q' ≤ q) :
    IsL2OrA7 L q' := by
  rcases h with h | ⟨r, k, hr, hr2, hq, hf⟩
  · exact Or.inl h
  · exact Or.inr ⟨r, k, hr, hr2, hqq.trans hq, hf⟩

theorem IsL2OrA7.isSimpleGroup {L : Type*} [Group L] {q : ℕ} (h : IsL2OrA7 L q) (hq : 4 ≤ q) :
    IsSimpleGroup L := by
  rcases h with hf | ⟨r, k, hr, -, hrk, hf⟩
  · obtain ⟨f⟩ := hf
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    exact f.isSimpleGroup
  · obtain ⟨f⟩ := hf
    have hk : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hrk
      omega
    have : IsSimpleGroup PSL(2, GaloisField r k) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [GaloisField.card r k hk]; omega)
    exact f.isSimpleGroup

theorem card_map_of_inf_ker_eq_bot {L : Type*} [Group L] (f : G →* L) (K : Subgroup G)
    (h : K ⊓ f.ker = ⊥) : Nat.card (K.map f) = Nat.card K := by
  have hinj : Function.Injective (f.comp K.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    have hk' : (k : G) ∈ K ⊓ f.ker := ⟨k.2, hk⟩
    rw [h, mem_bot] at hk'
    exact (mem_bot).mpr (Subtype.ext hk')
  have e := MonoidHom.ofInjective hinj
  rw [MonoidHom.range_comp, range_subtype] at e
  exact (Nat.card_congr e.toEquiv).symm

theorem le_sup_of_map_eq_top {L : Type*} [Group L] {N B Ō : Subgroup G} (f : N →* L)
    (hker : f.ker = Ō.subgroupOf N) (htop : (B.subgroupOf N).map f = ⊤) :
    N ≤ B ⊔ Ō := by
  intro n hn
  obtain ⟨b, hb, hbn⟩ := (mem_map).mp (htop ▸ mem_top (f ⟨n, hn⟩))
  have hk : b⁻¹ * ⟨n, hn⟩ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hbn, inv_mul_cancel]
  rw [hker, mem_subgroupOf] at hk
  have e : n = (b : G) * ((b⁻¹ * ⟨n, hn⟩ : N) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [e]
  exact mul_mem (mem_sup_left (mem_subgroupOf.mp hb)) (mem_sup_right hk)

theorem odd_natCard_O [Finite G] (H : Subgroup G) : Odd (Nat.card (O H)) := by
  rw [card_map_of_injective H.subtype_injective]
  exact CFSG.ABGLocalTools.odd_card_oddCore

theorem conj_mem_centralizer_of_mem_normalizer {V : Subgroup G} {k c : G}
    (hk : k ∈ normalizer (V : Set G)) (hc : c ∈ centralizer (V : Set G)) :
    k * c * k⁻¹ ∈ centralizer (V : Set G) := by
  rw [mem_centralizer_iff] at hc ⊢
  intro v hv
  have hv' : k⁻¹ * v * k⁻¹⁻¹ ∈ V := (mem_normalizer_iff.mp (inv_mem hk) v).mp hv
  rw [inv_inv] at hv'
  have h := hc _ hv'
  calc v * (k * c * k⁻¹) = k * ((k⁻¹ * v * k) * c) * k⁻¹ := by group
    _ = k * (c * (k⁻¹ * v * k)) * k⁻¹ := by rw [h]
    _ = k * c * k⁻¹ * v := by group

theorem exists_map_conj_eq_of_isSylowOf [Finite G] {p : ℕ} [Fact p.Prime] {P Q K : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P K) (hQ : CFSG.ABGLocalTools.IsSylowOf p Q K) :
    ∃ k ∈ K, P.map (MulAut.conj k).toMonoidHom = Q := by
  obtain ⟨S₁, rfl⟩ := hP
  obtain ⟨S₂, rfl⟩ := hQ
  obtain ⟨k, rfl⟩ := MulAction.exists_smul_eq K S₁ S₂
  refine ⟨k, k.2, ?_⟩
  ext y
  simp only [mem_map, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨k * u * k⁻¹, ?_, ?_⟩
    · simpa [MulAut.smul_def, mul_assoc] using hu
    · simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨(k⁻¹ * u * k : K), ⟨k⁻¹ * u * k, ?_, rfl⟩, ?_⟩
    · simpa [MulAut.smul_def, mul_assoc] using hu
    · simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group

theorem exists_mem_normalizer_of_conj_mem [Finite G] {H B Y : Subgroup G} (hBH : B ≤ H)
    (hYB : Y ≤ B) (hY : IsPGroup 2 Y) {m : G} (hmB : m ∈ B)
    (hm : ∀ y ∈ Y, ∃ y' ∈ Y, y'⁻¹ * (m * y * m⁻¹) ∈ O H) :
    ∃ n ∈ B, n ∈ normalizer (Y : Set G) ∧ n⁻¹ * m ∈ O H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO'n : B ≤ normalizer ((B ⊓ O H : Subgroup G) : Set G) := fun b hb =>
    inf_normalizer_le_normalizer_inf ⟨le_normalizer hb, le_normalizer_O H (hBH hb)⟩
  have hYO' : Y ≤ normalizer ((B ⊓ O H : Subgroup G) : Set G) := hYB.trans hO'n
  have hodd : Odd (Nat.card (B ⊓ O H : Subgroup G)) :=
    (odd_natCard_O H).of_dvd_nat (card_dvd_of_le inf_le_right)
  obtain ⟨k, hk⟩ := hY.exists_card_eq
  have hi : (B ⊓ O H) ⊓ Y = ⊥ := by
    refine inf_eq_bot_of_coprime ?_
    rw [hk]
    exact (Nat.coprime_two_right.mpr hodd).pow_right k
  have hcard :
      Nat.card ((B ⊓ O H) ⊔ Y : Subgroup G) = Nat.card (B ⊓ O H : Subgroup G) * Nat.card Y :=
    CFSG.CGT.Foote81L6.card_sup_of_le_normalizer hYO' hi
  have hYD : CFSG.ABGLocalTools.IsSylowOf 2 Y ((B ⊓ O H) ⊔ Y) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_sup_right, hY, ?_⟩
    have h1 := relIndex_mul_card (H := Y) (K := (B ⊓ O H) ⊔ Y)
    rw [inf_of_le_left (le_sup_right : Y ≤ (B ⊓ O H) ⊔ Y), hcard] at h1
    have hpos : 0 < Nat.card Y := Nat.card_pos
    have h2 : Y.relIndex ((B ⊓ O H) ⊔ Y) = Nat.card (B ⊓ O H : Subgroup G) :=
      Nat.eq_of_mul_eq_mul_right hpos h1
    rw [h2]
    exact hodd.not_two_dvd_nat
  have hY'D : Y.map (MulAut.conj m).toMonoidHom ≤ (B ⊓ O H) ⊔ Y := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨y', hy', ho⟩ := hm y hy
    change m * y * m⁻¹ ∈ (B ⊓ O H) ⊔ Y
    have hmy : y'⁻¹ * (m * y * m⁻¹) ∈ B :=
      mul_mem (inv_mem (hYB hy')) (mul_mem (mul_mem hmB (hYB hy)) (inv_mem hmB))
    have e : m * y * m⁻¹ = y' * (y'⁻¹ * (m * y * m⁻¹)) * y'⁻¹ * y' := by group
    rw [e]
    refine mul_mem (mem_sup_left ?_) (mem_sup_right hy')
    exact (mem_normalizer_iff.mp (hYO' hy') _).mp ⟨hmy, ho⟩
  have hY'syl : CFSG.ABGLocalTools.IsSylowOf 2 (Y.map (MulAut.conj m).toMonoidHom)
      ((B ⊓ O H) ⊔ Y) :=
    CFSG.ABGLocalTools.isSylowOf_of_card hY'D (by
      rw [card_map_of_injective (MulAut.conj m).injective, hYD.card_eq])
  obtain ⟨d, hdD, hd⟩ := exists_map_conj_eq_of_isSylowOf hYD hY'syl
  have hdD' : d ∈ ((B ⊓ O H : Subgroup G) : Set G) * (Y : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hYO']
    exact hdD
  obtain ⟨c, hc, y₀, hy₀, rfl⟩ := Set.mem_mul.mp hdD'
  have hcB : c ∈ B := (mem_inf.mp hc).1
  have hcO : c ∈ O H := (mem_inf.mp hc).2
  refine ⟨c⁻¹ * m, mul_mem (inv_mem hcB) hmB, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    have hle : Y.map (MulAut.conj (c⁻¹ * m)).toMonoidHom ≤ Y := by
      rintro _ ⟨y, hy, rfl⟩
      have hmy : m * y * m⁻¹ ∈ Y.map (MulAut.conj (c * y₀)).toMonoidHom := by
        rw [hd]
        exact ⟨y, hy, rfl⟩
      obtain ⟨y'', hy'', hy''e⟩ := hmy
      change c * y₀ * y'' * (c * y₀)⁻¹ = m * y * m⁻¹ at hy''e
      change c⁻¹ * m * y * (c⁻¹ * m)⁻¹ ∈ Y
      have e : c⁻¹ * m * y * (c⁻¹ * m)⁻¹ = y₀ * y'' * y₀⁻¹ := by
        calc c⁻¹ * m * y * (c⁻¹ * m)⁻¹ = c⁻¹ * (m * y * m⁻¹) * c := by group
          _ = c⁻¹ * (c * y₀ * y'' * (c * y₀)⁻¹) * c := by rw [hy''e]
          _ = y₀ * y'' * y₀⁻¹ := by group
      rw [e]
      exact mul_mem (mul_mem hy₀ hy'') (inv_mem hy₀)
    have heq : Y.map (MulAut.conj (c⁻¹ * m)).toMonoidHom = Y :=
      eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj _).injective])
    intro y
    constructor
    · intro hy
      exact heq ▸ ⟨y, hy, rfl⟩
    · intro hy
      rw [← heq] at hy
      obtain ⟨y₁, hy₁, hy₁e⟩ := hy
      change c⁻¹ * m * y₁ * (c⁻¹ * m)⁻¹ = c⁻¹ * m * y * (c⁻¹ * m)⁻¹ at hy₁e
      have : y₁ = y := by
        have := congrArg (fun z => (c⁻¹ * m)⁻¹ * z * (c⁻¹ * m)) hy₁e
        simpa [mul_assoc] using this
      exact this ▸ hy₁
  · have e : (c⁻¹ * m)⁻¹ * m = m⁻¹ * c * m⁻¹⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.mp (le_normalizer_O H (hBH (inv_mem hmB))) c).mp hcO

theorem mem_normalizer_sup_of_mem {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem le_inf_normalizer_sup_of_isSylowOf [Finite G] {p : ℕ} [Fact p.Prime] {R O H : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf p R O) (hOH : O ≤ H) (hHO : H ≤ normalizer (O : Set G)) :
    H ≤ (H ⊓ normalizer (R : Set G)) ⊔ O := by
  intro h hh
  have hOh : O.map (MulAut.conj h).toMonoidHom = O := (mem_normalizer_iff_map_conj_eq.mp (hHO hh))
  have hR' : CFSG.ABGLocalTools.IsSylowOf p (R.map (MulAut.conj h).toMonoidHom) O := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
    · rw [← hOh]
      exact map_mono hR.le
    · rw [card_map_of_injective (MulAut.conj h).injective, hR.card_eq]
  obtain ⟨o, ho, hoR⟩ := exists_map_conj_eq_of_isSylowOf hR' hR
  have hn : o * h ∈ normalizer (R : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    conv_rhs => rw [← hoR]
    rw [map_map]
    congr 1
    ext x
    change o * h * x * (o * h)⁻¹ = o * (h * x * h⁻¹) * o⁻¹
    group
  have e : h = (o * h) * (h⁻¹ * o⁻¹ * h) := by group
  rw [e]
  refine mul_mem (mem_sup_left ⟨mul_mem (hOH ho) hh, hn⟩) (mem_sup_right ?_)
  have := (mem_normalizer_iff.mp (hHO (inv_mem hh)) o⁻¹).mp (inv_mem ho)
  simpa using this

theorem mem_normalizer_centralizer_of_mem_normalizer {V : Subgroup G} {k : G}
    (hk : k ∈ normalizer (V : Set G)) : k ∈ normalizer (centralizer (V : Set G) : Set G) := by
  rw [mem_normalizer_iff]
  intro c
  refine ⟨fun hc => conj_mem_centralizer_of_mem_normalizer hk hc, fun hc => ?_⟩
  have := conj_mem_centralizer_of_mem_normalizer (inv_mem hk) hc
  simpa [mul_assoc] using this

theorem eq_of_inf_normalizer_le [Finite G] {p : ℕ} [Fact p.Prime] {U R : Subgroup G}
    (hR : IsPGroup p R) (hUR : U ≤ R) (h : R ⊓ normalizer (U : Set G) ≤ U) : R = U := by
  by_contra hne
  have hlt : U.subgroupOf R < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    refine hne (le_antisymm (fun r hr => ?_) hUR)
    have : (⟨r, hr⟩ : R) ∈ U.subgroupOf R := htop ▸ mem_top _
    exact this
  have : Group.IsNilpotent R := hR.isNilpotent
  obtain ⟨r, hrN, hrU⟩ := SetLike.exists_of_lt (normalizerCondition_of_isNilpotent _ hlt)
  refine hrU (h (mem_inf.mpr ⟨r.2, ?_⟩))
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact (mem_normalizer_iff.mp hrN ⟨g, hUR hg⟩).mp hg
  · intro hg
    have hgR : g ∈ R := by
      have h1 : (r : G) * g * (r : G)⁻¹ ∈ R := hUR hg
      have e : g = (r : G)⁻¹ * ((r : G) * g * (r : G)⁻¹) * r := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem r.2) h1) r.2
    exact (mem_normalizer_iff.mp hrN ⟨g, hgR⟩).mpr hg

theorem exists_isMaxInvIn_ge_of_le [Finite G] {p : ℕ} {A H S : Subgroup G} (hSH : S ≤ H)
    (hS : IsPGroup p S) (hAS : A ≤ normalizer (S : Set G)) :
    ∃ S' : Subgroup G, IsMaxInvIn p A H S' ∧ S ≤ S' := by
  classical
  obtain ⟨S', ⟨hS'H, hS'p, hAS', hSS'⟩, hmax⟩ :=
    Set.Finite.exists_maximalFor (fun T : Subgroup G => Nat.card T)
      {T : Subgroup G | T ≤ H ∧ IsPGroup p T ∧ A ≤ normalizer (T : Set G) ∧ S ≤ T}
      (Set.toFinite _) ⟨S, hSH, hS, hAS, le_rfl⟩
  refine ⟨S', ⟨hS'H, hS'p, hAS', fun T hTH hT hAT hS'T => ?_⟩, hSS'⟩
  have h := hmax ⟨hTH, hT, hAT, hSS'.trans hS'T⟩ (card_le_of_le hS'T)
  exact (eq_of_le_of_card_ge hS'T h).symm

end CFSG.GH72
