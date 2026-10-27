module

public import CFSG.GH74.GLS.SP.Local.SPLPumpXA
public import CFSG.GH74.GLS.SP.Local.SPLPumpXCtx
public import CFSG.GH74.GLS.TwoThin.G.Reduction
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionQuotient

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
open scoped commutatorElement

theorem exists_mul_of_mem_sup_normalizes {G : Type} [Group G] {N F : Subgroup G}
    (hF : F ≤ normalizer (N : Set G)) {x : G} (hx : x ∈ N ⊔ F) :
    ∃ n ∈ N, ∃ f ∈ F, n * f = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro y (hy | hy)
    · exact ⟨y, hy, 1, one_mem _, by simp⟩
    · exact ⟨1, one_mem _, y, hy, by simp⟩
  · exact ⟨1, one_mem _, 1, one_mem _, by simp⟩
  · rintro _ _ _ _ ⟨n₁, hn₁, f₁, hf₁, rfl⟩ ⟨n₂, hn₂, f₂, hf₂, rfl⟩
    have h1 : f₁ * n₂ * f₁⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hF hf₁) n₂).mp hn₂
    refine ⟨n₁ * (f₁ * n₂ * f₁⁻¹), mul_mem hn₁ h1, f₁ * f₂, mul_mem hf₁ hf₂, ?_⟩
    group
  · rintro _ _ ⟨n, hn, f, hf, rfl⟩
    have h1 : f⁻¹ * n⁻¹ * f⁻¹⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hF (inv_mem hf)) n⁻¹).mp (inv_mem hn)
    refine ⟨f⁻¹ * n⁻¹ * f⁻¹⁻¹, h1, f⁻¹, inv_mem hf, ?_⟩
    group

theorem perfect_le_of_solvable {G : Type} [Group G] [Finite G] {N F P : Subgroup G}
    (hF : Group.IsSolvable ↥F) (hnorm : F ≤ normalizer (N : Set G)) (hP : ⁅P, P⁆ = P)
    (hPle : P ≤ N ⊔ F) : P ≤ N := by
  set W := N ⊔ F with hW
  have hNW : N ≤ W := le_sup_left
  have hFW : F ≤ W := le_sup_right
  have hWn : W ≤ normalizer (N : Set G) := sup_le le_normalizer hnorm
  have hnormal : (N.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff hNW).mpr fun h k hh hk =>
      (Subgroup.mem_normalizer_iff.mp (hWn hk) h).mp hh
  let φ : ↥W →* ↥W ⧸ N.subgroupOf W := QuotientGroup.mk' (N.subgroupOf W)
  let θ : ↥F →* ↥W ⧸ N.subgroupOf W := φ.comp (Subgroup.inclusion hFW)
  have hθ : Function.Surjective θ := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hsup : (N ⊔ F).subgroupOf W = N.subgroupOf W ⊔ F.subgroupOf W :=
      Subgroup.subgroupOf_sup hNW hFW
    have hy' : (⟨x, hx⟩ : ↥W) ∈ N.subgroupOf W ⊔ F.subgroupOf W := by
      rw [← hsup, Subgroup.mem_subgroupOf]
      exact hx
    obtain ⟨n', hn', f', hf', hnf⟩ := Subgroup.mem_sup_of_normal_left.mp hy'
    refine ⟨⟨(f' : G), Subgroup.mem_subgroupOf.mp hf'⟩, ?_⟩
    show φ (Subgroup.inclusion hFW ⟨(f' : G), Subgroup.mem_subgroupOf.mp hf'⟩) = φ ⟨x, hx⟩
    have hincl : Subgroup.inclusion hFW ⟨(f' : G), Subgroup.mem_subgroupOf.mp hf'⟩ = f' := rfl
    rw [hincl, ← hnf, map_mul]
    have : φ n' = 1 := (QuotientGroup.eq_one_iff n').mpr hn'
    rw [this, one_mul]
  have hsolv : Group.IsSolvable (↥W ⧸ N.subgroupOf W) := Group.isSolvable_of_surjective hθ
  set P' : Subgroup ↥W := P.subgroupOf W with hP'
  have hPW : P ≤ W := hPle
  have hperf : ⁅P', P'⁆ = P' := by
    apply Subgroup.map_injective W.subtype_injective
    rw [Subgroup.map_commutator, hP', Subgroup.map_subgroupOf_eq_of_le hPW, hP]
  have hperfmap : ⁅P'.map φ, P'.map φ⁆ = P'.map φ := by
    rw [← Subgroup.map_commutator, hperf]
  have hbot : P'.map φ = ⊥ := by
    by_contra hne
    have hnt : Nontrivial ↥(P'.map φ) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have : Group.IsPerfect ↥(P'.map φ) := Subgroup.isPerfect_iff.mpr hperfmap
    have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥(P'.map φ)
    have h2 : commutator ↥(P'.map φ) = ⊤ := Group.IsPerfect.commutator_eq_top
    rw [h2] at h1
    exact lt_irrefl _ h1
  intro x hx
  have hxW : (⟨x, hPW hx⟩ : ↥W) ∈ P' := hx
  have h1 : φ ⟨x, hPW hx⟩ ∈ P'.map φ := ⟨_, hxW, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

noncomputable abbrev barT {G : Type} [Group G] [Finite G] (t : G) (H : Subgroup G) :
    Subgroup (barQ ↥(centralizer ({t} : Set G))) :=
  (H.subgroupOf (centralizer ({t} : Set G))).map (barMk ↥(centralizer ({t} : Set G)))

namespace PumpXSetting

variable {G : Type} [Group G] [Finite G] {q : ℕ} {z t : G} {I F₀ : Subgroup G}
  (S : PumpXSetting G q z t I F₀)

include S

theorem z_mem_Y : z ∈ centralizer ({t} : Set G) := S.z_mem_W.2

theorem t_mem_Y : t ∈ centralizer ({t} : Set G) := S.t_mem_W.2

theorem I_le_Y : I ≤ centralizer ({t} : Set G) := S.I_le_W.trans inf_le_right

noncomputable def etaI : ↥I →* barQ ↥(centralizer ({t} : Set G)) :=
  (barMk ↥(centralizer ({t} : Set G))).comp (Subgroup.inclusion S.I_le_Y)

theorem etaI_injective : Function.Injective S.etaI := by
  have := S.I_simple
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← MonoidHom.ker_eq_bot_iff]
  have hn : S.etaI.ker.Normal := MonoidHom.normal_ker S.etaI
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S.etaI.ker with h | h
  · exact h
  · exfalso
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥I) 2 (even_iff_two_dvd.mp S.I_even)
    have hxk : x ∈ S.etaI.ker := h ▸ Subgroup.mem_top x
    have h1 : barMk ↥(centralizer ({t} : Set G)) (Subgroup.inclusion S.I_le_Y x) = 1 := hxk
    have hmem : Subgroup.inclusion S.I_le_Y x ∈ pPrimeCore 2 ↥(centralizer ({t} : Set G)) :=
      (QuotientGroup.eq_one_iff _).mp h1
    have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
    have hord : orderOf (Subgroup.inclusion S.I_le_Y x) = 2 := by
      rw [← hx]
      exact orderOf_injective _ (Subgroup.inclusion_injective S.I_le_Y) x
    rw [hord] at hdvd
    exact (Nat.not_even_iff_odd.mpr (odd_card_pPrimeCore _)) (even_iff_two_dvd.mpr hdvd)

theorem mem_A_iff {x : barQ ↥(centralizer ({t} : Set G))} :
    x ∈ (I.subgroupOf (centralizer ({t} : Set G))).map (barMk ↥(centralizer ({t} : Set G))) ↔
      ∃ i : ↥I, S.etaI i = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨(y : G), hy⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Subgroup.inclusion S.I_le_Y i, i.2, rfl⟩

theorem mem_W_of_cen {w : ↥(centralizer ({t} : Set G))}
    (hw : w * ⟨z, S.z_mem_Y⟩ = ⟨z, S.z_mem_Y⟩ * w) :
    (w : G) ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) := by
  refine Subgroup.mem_inf.mpr ⟨?_, w.2⟩
  rw [mem_centralizer_singleton_iff]
  exact congrArg Subtype.val hw

theorem exists_W_of_cen {c : barQ ↥(centralizer ({t} : Set G))}
    (hc : barMk _ ⟨z, S.z_mem_Y⟩ * c = c * barMk _ ⟨z, S.z_mem_Y⟩) :
    ∃ w : ↥(centralizer ({t} : Set G)),
      (w : G) ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) ∧ barMk _ w = c := by
  have hs : orderOf (⟨z, S.z_mem_Y⟩ : ↥(centralizer ({t} : Set G))) = 2 :=
    orderOf_mk_centralizer S.z_mem_Y S.z_ord
  have hmem : c ∈ centralizer ({barMk _ ⟨z, S.z_mem_Y⟩} : Set (barQ ↥(centralizer ({t} : Set G)))) := by
    rw [mem_centralizer_singleton_iff]
    exact hc.symm
  rw [← map_centralizer_barMk hs] at hmem
  obtain ⟨w, hw, rfl⟩ := hmem
  exact ⟨w, S.mem_W_of_cen (mem_centralizer_singleton_iff.mp hw), rfl⟩

theorem F₀_le_normalizer_N : F₀ ≤ normalizer ((zpowers z ⊔ zpowers t ⊔ I : Subgroup G) : Set G) :=
  fun f hf => mem_normalizer_of_conj (S.F₀_conj_N hf)
    (fun n hn => by simpa using S.F₀_conj_N (inv_mem hf) n hn)

theorem W_decomp : ∀ w ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G),
    ∃ n ∈ zpowers z ⊔ zpowers t ⊔ I, ∃ f ∈ F₀, n * f = w := by
  intro w hw
  rw [S.W_eq_sup] at hw
  exact exists_mul_of_mem_sup_normalizes S.F₀_le_normalizer_N hw

theorem map_Zb {ζ : G} (hζ : ζ ∈ zpowers z ⊔ zpowers t) (hζY : ζ ∈ centralizer ({t} : Set G)) :
    barMk ↥(centralizer ({t} : Set G)) ⟨ζ, hζY⟩ ∈
      zpowers (barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩) ⊔
        zpowers (barMk ↥(centralizer ({t} : Set G)) ⟨t, S.t_mem_Y⟩) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_comm (A := zpowers z) (B := zpowers t) (fun a ha b hb => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow (show Commute z t from S.zt_comm) k l).eq) hζ
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have : (⟨z ^ k * t ^ l, hζY⟩ : ↥(centralizer ({t} : Set G))) =
      (⟨z, S.z_mem_Y⟩ : ↥(centralizer ({t} : Set G))) ^ k * (⟨t, S.t_mem_Y⟩ : ↥(centralizer ({t} : Set G))) ^ l :=
    Subtype.ext (by simp)
  rw [this, map_mul, map_zpow, map_zpow]
  exact mul_mem_sup (Subgroup.zpow_mem_zpowers _ _) (Subgroup.zpow_mem_zpowers _ _)

theorem z_sq' : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rwa [S.z_ord, sq] at this

theorem t_sq' : t * t = 1 := by
  have := pow_orderOf_eq_one t
  rwa [S.t_ord, sq] at this

theorem orderOf_zbar : orderOf (barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩) = 2 :=
  orderOf_barMk (orderOf_mk_centralizer S.z_mem_Y S.z_ord)

theorem orderOf_tbar : orderOf (barMk ↥(centralizer ({t} : Set G)) ⟨t, S.t_mem_Y⟩) = 2 :=
  orderOf_barMk (orderOf_mk_centralizer S.t_mem_Y S.t_ord)

theorem zbar_ne_tbar : barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩ ≠
    barMk ↥(centralizer ({t} : Set G)) ⟨t, S.t_mem_Y⟩ := by
  intro h
  set g : ↥(centralizer ({t} : Set G)) := ⟨z, S.z_mem_Y⟩ * ⟨t, S.t_mem_Y⟩⁻¹ with hg
  have h1 : barMk ↥(centralizer ({t} : Set G)) g = 1 := by
    rw [hg, map_mul, map_inv, h, mul_inv_cancel]
  have hmem : g ∈ pPrimeCore 2 ↥(centralizer ({t} : Set G)) := (QuotientGroup.eq_one_iff _).mp h1
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right S.t_sq'
  have hg2 : g ^ 2 = 1 := by
    apply Subtype.ext
    simp only [hg, Subgroup.coe_mul, Subgroup.coe_inv, htinv, sq, Subgroup.coe_one]
    calc z * t * (z * t) = z * (t * z) * t := by group
      _ = z * (z * t) * t := by rw [S.zt_comm]
      _ = (z * z) * (t * t) := by group
      _ = 1 := by rw [S.z_sq', S.t_sq', one_mul]
  have hg1 : g ≠ 1 := by
    intro h'
    apply S.z_ne_t
    have := congrArg Subtype.val h'
    simp only [hg, Subgroup.coe_mul, Subgroup.coe_inv, htinv, Subgroup.coe_one] at this
    calc z = z * t * t := by rw [mul_assoc, S.t_sq', mul_one]
      _ = t := by rw [this, one_mul]
  have hord : orderOf g = 2 := orderOf_eq_prime hg2 hg1
  have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
  rw [hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr (odd_card_pPrimeCore _)) (even_iff_two_dvd.mpr hdvd)

theorem tbar_central (x : barQ ↥(centralizer ({t} : Set G))) :
    x * barMk ↥(centralizer ({t} : Set G)) ⟨t, S.t_mem_Y⟩ =
      barMk ↥(centralizer ({t} : Set G)) ⟨t, S.t_mem_Y⟩ * x := by
  obtain ⟨y, rfl⟩ := barMk_surjective (Y := ↥(centralizer ({t} : Set G))) x
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp y.2)

theorem A_L2' : ∃ q' : ℕ, Odd q' ∧ 5 ≤ q' ∧ IVK.IsL2
    ↥((I.subgroupOf (centralizer ({t} : Set G))).map (barMk ↥(centralizer ({t} : Set G))))
      (fun r => r = q') := by
  obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := S.I_L2
  refine ⟨q, S.odd_q, S.q_ge, F, hF, hFin, hq, ⟨?_⟩⟩
  have hA : (I.subgroupOf (centralizer ({t} : Set G))).map (barMk ↥(centralizer ({t} : Set G))) =
      S.etaI.range := by
    ext x
    rw [S.mem_A_iff, MonoidHom.mem_range]
  exact ((MulEquiv.subgroupCongr hA).trans (MonoidHom.ofInjective S.etaI_injective).symm).trans e

theorem A_perf' : ⁅barT t I, barT t I⁆ = barT t I := by
  have hperf : ⁅I.subgroupOf (centralizer ({t} : Set G)), I.subgroupOf (centralizer ({t} : Set G))⁆ =
      I.subgroupOf (centralizer ({t} : Set G)) := by
    apply Subgroup.map_injective (centralizer ({t} : Set G)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le S.I_le_Y, S.I_perf]
  show ⁅(I.subgroupOf (centralizer ({t} : Set G))).map (barMk ↥(centralizer ({t} : Set G))),
    (I.subgroupOf (centralizer ({t} : Set G))).map (barMk ↥(centralizer ({t} : Set G)))⁆ = _
  rw [← Subgroup.map_commutator, hperf]

theorem A_cen' : ∀ a ∈ (I.subgroupOf (centralizer ({t} : Set G))).map
    (barMk ↥(centralizer ({t} : Set G))),
    barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩ * a =
      a * barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩ := by
  intro a ha
  obtain ⟨i, rfl⟩ := (S.mem_A_iff).mp ha
  show barMk _ ⟨z, S.z_mem_Y⟩ * barMk _ (Subgroup.inclusion S.I_le_Y i) =
    barMk _ (Subgroup.inclusion S.I_le_Y i) * barMk _ ⟨z, S.z_mem_Y⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (S.I_le_W i.2).1).symm

theorem A_norm' : ∀ c : barQ ↥(centralizer ({t} : Set G)),
    barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩ * c =
      c * barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩ →
    ∀ a ∈ (I.subgroupOf (centralizer ({t} : Set G))).map (barMk ↥(centralizer ({t} : Set G))),
      c * a * c⁻¹ ∈ (I.subgroupOf (centralizer ({t} : Set G))).map
        (barMk ↥(centralizer ({t} : Set G))) := by
  intro c hc a ha
  obtain ⟨w, hw, rfl⟩ := S.exists_W_of_cen hc
  obtain ⟨i, rfl⟩ := (S.mem_A_iff).mp ha
  have hj : (w : G) * (i : G) * (w : G)⁻¹ ∈ I := S.W_normalizes_I (w : G) hw i i.2
  refine (S.mem_A_iff).mpr ⟨⟨(w : G) * (i : G) * (w : G)⁻¹, hj⟩, ?_⟩
  show barMk _ (Subgroup.inclusion S.I_le_Y ⟨(w : G) * (i : G) * (w : G)⁻¹, hj⟩) =
    barMk _ w * barMk _ (Subgroup.inclusion S.I_le_Y i) * (barMk _ w)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem map_N {n : G} (hn : n ∈ zpowers z ⊔ zpowers t ⊔ I) (hnY : n ∈ centralizer ({t} : Set G)) :
    barMk ↥(centralizer ({t} : Set G)) ⟨n, hnY⟩ ∈
      (zpowers (barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩) ⊔
        zpowers (barMk ↥(centralizer ({t} : Set G)) ⟨t, S.t_mem_Y⟩)) ⊔
      (I.subgroupOf (centralizer ({t} : Set G))).map (barMk ↥(centralizer ({t} : Set G))) := by
  obtain ⟨ζ, hζ, i, hi, rfl⟩ := mem_sup_of_comm (A := zpowers z ⊔ zpowers t) (B := I)
    (fun a ha b hb => zt_comm_W a ha b (S.I_le_W hb)) hn
  have hζY : ζ ∈ centralizer ({t} : Set G) := by
    have h1 : ζ * i ∈ centralizer ({t} : Set G) := hnY
    have h2 : i ∈ centralizer ({t} : Set G) := S.I_le_Y hi
    have := mul_mem h1 (inv_mem h2)
    simpa using this
  have : (⟨ζ * i, hnY⟩ : ↥(centralizer ({t} : Set G))) = ⟨ζ, hζY⟩ * ⟨i, S.I_le_Y hi⟩ := rfl
  rw [this, map_mul]
  refine mul_mem_sup (S.map_Zb hζ hζY) ?_
  exact (S.mem_A_iff).mpr ⟨⟨i, hi⟩, rfl⟩

theorem odd_card_Fbar : Odd (Nat.card ↥((F₀.subgroupOf (centralizer ({t} : Set G))).map
    (barMk ↥(centralizer ({t} : Set G))))) := by
  have h1 := Subgroup.card_map_dvd (H := F₀.subgroupOf (centralizer ({t} : Set G)))
    (barMk ↥(centralizer ({t} : Set G)))
  have h2 : Nat.card ↥(F₀.subgroupOf (centralizer ({t} : Set G))) = Nat.card ↥F₀ := by
    have hF₀Y : F₀ ≤ centralizer ({t} : Set G) := S.F₀_le_W.trans inf_le_right
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF₀Y).toEquiv
  rw [h2] at h1
  exact S.F₀_odd.of_dvd_nat h1

theorem Fbar_le_normalizer_Nbar :
    (F₀.subgroupOf (centralizer ({t} : Set G))).map (barMk ↥(centralizer ({t} : Set G))) ≤
      normalizer (((zpowers z ⊔ zpowers t ⊔ I).subgroupOf (centralizer ({t} : Set G))).map
        (barMk ↥(centralizer ({t} : Set G))) : Set (barQ ↥(centralizer ({t} : Set G)))) := by
  have key : ∀ x ∈ (F₀.subgroupOf (centralizer ({t} : Set G))).map
      (barMk ↥(centralizer ({t} : Set G))),
      ∀ y ∈ ((zpowers z ⊔ zpowers t ⊔ I).subgroupOf (centralizer ({t} : Set G))).map
        (barMk ↥(centralizer ({t} : Set G))),
      x * y * x⁻¹ ∈ ((zpowers z ⊔ zpowers t ⊔ I).subgroupOf (centralizer ({t} : Set G))).map
        (barMk ↥(centralizer ({t} : Set G))) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    refine ⟨a * b * a⁻¹, ?_, by simp⟩
    exact S.F₀_conj_N (f := (a : G)) ha (b : G) hb
  intro x hx
  exact mem_normalizer_of_conj (key x hx)
    (fun y hy => by simpa using key x⁻¹ (inv_mem hx) y hy)

theorem cen_le_sup : ∀ c : barQ ↥(centralizer ({t} : Set G)),
    barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩ * c =
      c * barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩ →
    c ∈ ((zpowers z ⊔ zpowers t ⊔ I).subgroupOf (centralizer ({t} : Set G))).map
        (barMk ↥(centralizer ({t} : Set G))) ⊔
      (F₀.subgroupOf (centralizer ({t} : Set G))).map (barMk ↥(centralizer ({t} : Set G))) := by
  intro c hc
  obtain ⟨w, hw, rfl⟩ := S.exists_W_of_cen hc
  obtain ⟨n, hn, f, hf, hnf⟩ := S.W_decomp (w : G) hw
  have hnY : n ∈ centralizer ({t} : Set G) := S.N_le_W hn |>.2
  have hfY : f ∈ centralizer ({t} : Set G) := S.F₀_le_W hf |>.2
  have hwnf : w = ⟨n, hnY⟩ * ⟨f, hfY⟩ := Subtype.ext hnf.symm
  rw [hwnf, map_mul]
  exact mul_mem_sup ⟨⟨n, hnY⟩, hn, rfl⟩ ⟨⟨f, hfY⟩, hf, rfl⟩

theorem Nbar_le : ((zpowers z ⊔ zpowers t ⊔ I).subgroupOf (centralizer ({t} : Set G))).map
      (barMk ↥(centralizer ({t} : Set G))) ≤
    (zpowers (barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩) ⊔
        zpowers (barMk ↥(centralizer ({t} : Set G)) ⟨t, S.t_mem_Y⟩)) ⊔
      (I.subgroupOf (centralizer ({t} : Set G))).map (barMk ↥(centralizer ({t} : Set G))) := by
  rintro _ ⟨b, hb, rfl⟩
  exact S.map_N hb b.2

theorem two_elt' : ∀ c : barQ ↥(centralizer ({t} : Set G)),
    barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩ * c =
      c * barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩ → (∃ k : ℕ, c ^ (2 ^ k) = 1) →
    c ∈ zpowers (barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩) ⊔
      zpowers (barMk ↥(centralizer ({t} : Set G)) ⟨t, S.t_mem_Y⟩) ⊔
      (I.subgroupOf (centralizer ({t} : Set G))).map (barMk ↥(centralizer ({t} : Set G))) := by
  intro c hc h2
  have h1 := two_mem_sup_of_odd S.odd_card_Fbar S.Fbar_le_normalizer_Nbar c (S.cen_le_sup c hc) h2
  exact S.Nbar_le h1

theorem cen_A' : ∀ c : barQ ↥(centralizer ({t} : Set G)),
    barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩ * c =
      c * barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩ →
    (∀ a ∈ (I.subgroupOf (centralizer ({t} : Set G))).map (barMk ↥(centralizer ({t} : Set G))),
      c * a = a * c) →
    c ∈ zpowers (barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩) ⊔
      zpowers (barMk ↥(centralizer ({t} : Set G)) ⟨t, S.t_mem_Y⟩) := by
  intro c hc hca
  obtain ⟨w, hw, rfl⟩ := S.exists_W_of_cen hc
  have hcomm : ∀ i ∈ I, (w : G) * i = i * (w : G) := by
    intro i hi
    have hj : (w : G) * i * (w : G)⁻¹ * i⁻¹ ∈ I :=
      mul_mem (S.W_normalizes_I (w : G) hw i hi) (inv_mem hi)
    have h1 : S.etaI ⟨(w : G) * i * (w : G)⁻¹ * i⁻¹, hj⟩ = 1 := by
      have hA : S.etaI ⟨i, hi⟩ ∈ (I.subgroupOf (centralizer ({t} : Set G))).map
          (barMk ↥(centralizer ({t} : Set G))) := (S.mem_A_iff).mpr ⟨⟨i, hi⟩, rfl⟩
      have := hca _ hA
      show barMk _ (Subgroup.inclusion S.I_le_Y ⟨(w : G) * i * (w : G)⁻¹ * i⁻¹, hj⟩) = 1
      have e : Subgroup.inclusion S.I_le_Y ⟨(w : G) * i * (w : G)⁻¹ * i⁻¹, hj⟩ =
          w * ⟨i, S.I_le_Y hi⟩ * w⁻¹ * ⟨i, S.I_le_Y hi⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
      change barMk _ w * barMk _ (Subgroup.inclusion S.I_le_Y ⟨i, hi⟩) * (barMk _ w)⁻¹ *
        (barMk _ (Subgroup.inclusion S.I_le_Y ⟨i, hi⟩))⁻¹ = 1
      have hc' : barMk _ w * barMk _ (Subgroup.inclusion S.I_le_Y ⟨i, hi⟩) =
          barMk _ (Subgroup.inclusion S.I_le_Y ⟨i, hi⟩) * barMk _ w := this
      rw [hc']
      group
    have h2 := S.etaI_injective (h1.trans (map_one S.etaI).symm)
    have h3 := congrArg Subtype.val h2
    simp only [Subgroup.coe_one] at h3
    calc (w : G) * i = (w : G) * i * (w : G)⁻¹ * i⁻¹ * (i * (w : G)) := by group
      _ = i * (w : G) := by rw [h3, one_mul]
  have hmem := S.W_cen_mem (w : G) hw hcomm
  exact S.map_Zb hmem w.2

theorem perfect_le' : ∀ P : Subgroup (barQ ↥(centralizer ({t} : Set G))),
    (∀ c ∈ P, barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩ * c =
      c * barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩) → ⁅P, P⁆ = P →
    P ≤ (I.subgroupOf (centralizer ({t} : Set G))).map (barMk ↥(centralizer ({t} : Set G))) := by
  intro P hPc hP
  set X := barQ ↥(centralizer ({t} : Set G)) with hX
  set Ab : Subgroup X := (I.subgroupOf (centralizer ({t} : Set G))).map
    (barMk ↥(centralizer ({t} : Set G))) with hAb
  set Nb : Subgroup X := ((zpowers z ⊔ zpowers t ⊔ I).subgroupOf (centralizer ({t} : Set G))).map
    (barMk ↥(centralizer ({t} : Set G))) with hNb
  set Fb : Subgroup X := (F₀.subgroupOf (centralizer ({t} : Set G))).map
    (barMk ↥(centralizer ({t} : Set G))) with hFb
  set zb : X := barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩ with hzb
  set tb : X := barMk ↥(centralizer ({t} : Set G)) ⟨t, S.t_mem_Y⟩ with htb
  set Zb : Subgroup X := zpowers zb ⊔ zpowers tb with hZb
  have hPle : P ≤ Nb ⊔ Fb := fun c hc => S.cen_le_sup c (hPc c hc)
  have hFsolv : Group.IsSolvable ↥Fb := CFSG.FeitThompson.isSolvable_of_odd_natCard _ S.odd_card_Fbar
  have hPN : P ≤ Nb := perfect_le_of_solvable hFsolv S.Fbar_le_normalizer_Nbar hP hPle
  have hPZA : P ≤ Ab ⊔ Zb := by
    intro c hc
    rw [sup_comm]
    exact S.Nbar_le (hPN hc)
  have htcen : ∀ b ∈ zpowers tb, ∀ x : X, b * x = x * b := by
    intro b hb x
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (((show Commute x tb from S.tbar_central x).zpow_right l).eq).symm
  have hZA : ∀ ζ ∈ Zb, ∀ a ∈ Ab, ζ * a = a * ζ := by
    have hz : ∀ a ∈ Ab, zb * a = a * zb := S.A_cen'
    have hle : Zb ≤ centralizer (Ab : Set X) := by
      refine sup_le ?_ ?_
      · rw [zpowers_le, mem_centralizer_iff]
        intro a ha
        exact (hz a ha).symm
      · rw [zpowers_le, mem_centralizer_iff]
        intro a ha
        exact S.tbar_central a
    intro ζ hζ a ha
    exact (mem_centralizer_iff.mp (hle hζ) a ha).symm
  have hZab : ∀ ζ ∈ Zb, ∀ ζ' ∈ Zb, ζ * ζ' = ζ' * ζ := by
    have hcomm : ∀ a ∈ zpowers zb, ∀ b ∈ zpowers tb, a * b = b * a :=
      fun a _ b hb => (htcen b hb a).symm
    intro ζ hζ ζ' hζ'
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_comm hcomm hζ
    obtain ⟨a', ha', b', hb', rfl⟩ := mem_sup_of_comm hcomm hζ'
    have haa : a * a' = a' * a := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨k', rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
      exact (Commute.zpow_zpow_self zb k k').eq
    have hbb : b * b' = b' * b := by
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      obtain ⟨l', rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
      exact (Commute.zpow_zpow_self tb l l').eq
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [htcen b hb a']
      _ = a * a' * (b * b') := by group
      _ = a' * a * (b' * b) := by rw [haa, hbb]
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [← htcen b' hb' a]
      _ = a' * b' * (a * b) := by group
  have hZsolv : Group.IsSolvable ↥Zb := by
    refine Group.isSolvable_of_comm ?_
    intro a b
    exact Subtype.ext (hZab a.1 a.2 b.1 b.2)
  have hZnorm : Zb ≤ normalizer (Ab : Set X) := fun ζ hζ =>
    mem_normalizer_of_comm (fun a ha => hZA ζ hζ a ha)
  exact perfect_le_of_solvable hZsolv hZnorm hP hPZA

section Sylow

variable {T₁ : Subgroup G}

omit S in
theorem Tbar_le (hT₁I : T₁ ≤ I) : barT t T₁ ≤ barT t I := by
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a, hT₁I ha, rfl⟩

omit S in
theorem Tbar_pgrp (hT₁p : IsPGroup 2 T₁) : IsPGroup 2 ↥(barT t T₁) := by
  intro x
  obtain ⟨a, ha, hax⟩ := x.2
  obtain ⟨k, hk⟩ := hT₁p ⟨(a : G), ha⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : (a : G) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h2 : a ^ (2 ^ k) = 1 := Subtype.ext h1
  show (x : barQ ↥(centralizer ({t} : Set G))) ^ (2 ^ k) = 1
  rw [← hax, ← map_pow, h2, map_one]

theorem Tbar_eq (hT₁I : T₁ ≤ I) : barT t T₁ = (T₁.subgroupOf I).map S.etaI := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨(a : G), hT₁I ha⟩, ha, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨Subgroup.inclusion S.I_le_Y i, hi, rfl⟩

theorem card_Tbar (hT₁I : T₁ ≤ I) : Nat.card ↥(barT t T₁) = Nat.card ↥T₁ := by
  rw [S.Tbar_eq hT₁I, Subgroup.card_map_of_injective S.etaI_injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₁I).toEquiv

theorem Tbar_max (hT₁I : T₁ ≤ I)
    (hmax : ∀ P : Subgroup G, P ≤ I → IsPGroup 2 P → T₁ ≤ P → P = T₁) :
    ∀ P : Subgroup (barQ ↥(centralizer ({t} : Set G))), P ≤ barT t I → IsPGroup 2 P →
      barT t T₁ ≤ P → P = barT t T₁ := by
  intro P hPA hPp hTP
  set W' : Subgroup G := (P.comap S.etaI).map I.subtype with hW'
  have hW'I : W' ≤ I := Subgroup.map_subtype_le _
  have hW'mem : ∀ g : G, g ∈ W' ↔ ∃ i : ↥I, (i : G) = g ∧ S.etaI i ∈ P := by
    intro g
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, rfl, hi⟩
    · rintro ⟨i, rfl, hi⟩
      exact ⟨i, hi, rfl⟩
  have hW'p : IsPGroup 2 ↥W' := by
    intro g
    obtain ⟨i, hig, hi⟩ := (hW'mem g.1).mp g.2
    obtain ⟨k, hk⟩ := hPp ⟨S.etaI i, hi⟩
    have h1 : S.etaI (i ^ (2 ^ k)) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have h2 : i ^ (2 ^ k) = 1 := S.etaI_injective (h1.trans (map_one S.etaI).symm)
    refine ⟨k, Subtype.ext ?_⟩
    show (g : G) ^ (2 ^ k) = 1
    rw [← hig]
    exact congrArg Subtype.val h2
  have hTW' : T₁ ≤ W' := by
    intro g hg
    refine (hW'mem g).mpr ⟨⟨g, hT₁I hg⟩, rfl, ?_⟩
    exact hTP ⟨⟨g, S.I_le_Y (hT₁I hg)⟩, hg, rfl⟩
  have hWT : W' = T₁ := hmax W' hW'I hW'p hTW'
  refine le_antisymm ?_ hTP
  intro x hx
  obtain ⟨i, rfl⟩ := (S.mem_A_iff).mp (hPA hx)
  have hiW : (i : G) ∈ W' := (hW'mem _).mpr ⟨i, rfl, hx⟩
  rw [hWT] at hiW
  exact ⟨⟨(i : G), S.I_le_Y i.2⟩, hiW, rfl⟩

theorem bound'
    (hbound : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({t} : Set G) →
      Nat.card ↥P ≤ 2 * Nat.card ↥T₁ ^ 2) (hT₁I : T₁ ≤ I) :
    ∀ P : Subgroup (barQ ↥(centralizer ({t} : Set G))), IsPGroup 2 P →
      Nat.card ↥P ≤ 2 * Nat.card ↥(barT t T₁) ^ 2 := by
  intro P hP
  obtain ⟨W, -, hWp, hWc, -⟩ := CFSG.ComponentClassification.AschbacherTheorem5.Involution.exists_isPGroup_lift
    (pPrimeCore 2 ↥(centralizer ({t} : Set G))) (odd_card_pPrimeCore _) (C := ⊤) (V := P) hP
    (fun x _ => by
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨y, Subgroup.mem_top y, rfl⟩)
  have hinj := (centralizer ({t} : Set G)).subtype_injective
  have hW'p : IsPGroup 2 ↥(W.map (centralizer ({t} : Set G)).subtype) :=
    hWp.of_equiv (Subgroup.equivMapOfInjective W _ hinj)
  have hW'c : Nat.card ↥(W.map (centralizer ({t} : Set G)).subtype) = Nat.card ↥W :=
    (Subgroup.card_map_of_injective hinj).symm ▸ rfl
  have h1 := hbound (W.map (centralizer ({t} : Set G)).subtype) hW'p (Subgroup.map_subtype_le W)
  rw [hW'c, hWc, ← S.card_Tbar hT₁I] at h1
  exact h1

end Sylow

theorem xctx : ∃ T : Subgroup (barQ ↥(centralizer ({t} : Set G))),
    XCtx (barQ ↥(centralizer ({t} : Set G))) (barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩)
      (barMk ↥(centralizer ({t} : Set G)) ⟨t, S.t_mem_Y⟩) (barT t I) T := by
  obtain ⟨T₁, hT₁I, hT₁p, hT₁max, hbound⟩ := S.T₁ex
  refine ⟨barT t T₁, ?_⟩
  have hzsq : barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩ *
      barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩ = 1 := by
    have := pow_orderOf_eq_one (barMk ↥(centralizer ({t} : Set G)) ⟨z, S.z_mem_Y⟩)
    rwa [S.orderOf_zbar, sq] at this
  have htsq : barMk ↥(centralizer ({t} : Set G)) ⟨t, S.t_mem_Y⟩ *
      barMk ↥(centralizer ({t} : Set G)) ⟨t, S.t_mem_Y⟩ = 1 := by
    have := pow_orderOf_eq_one (barMk ↥(centralizer ({t} : Set G)) ⟨t, S.t_mem_Y⟩)
    rwa [S.orderOf_tbar, sq] at this
  refine
    { z_sq := hzsq
      z_ne_one := ?_
      t_sq := htsq
      t_ne_one := ?_
      zt_ne := S.zbar_ne_tbar
      t_central := S.tbar_central
      A_L2 := S.A_L2'
      A_perf := S.A_perf'
      A_cen := S.A_cen'
      A_norm := S.A_norm'
      two_elt := S.two_elt'
      cen_A := S.cen_A'
      perfect_le := S.perfect_le'
      T₁_le := Tbar_le hT₁I
      T₁_pgrp := Tbar_pgrp hT₁p
      T₁_max := S.Tbar_max hT₁I hT₁max
      bound := S.bound' hbound hT₁I
      gen4 := gen4_barQ S.gen4 t }
  · intro h
    have := S.orderOf_zbar
    rw [h, orderOf_one] at this
    omega
  · intro h
    have := S.orderOf_tbar
    rw [h, orderOf_one] at this
    omega

end PumpXSetting

end CFSG.GH74.GLS.SP.Local
