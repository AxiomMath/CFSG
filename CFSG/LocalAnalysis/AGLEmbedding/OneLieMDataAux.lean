module

import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorel
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoDataAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorusFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem exists_gen_pow {p n e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 2 ≤ n)
    (he : e = 1 ∨ e = 2) :
    ∃ γ : (GaloisField p n)ˣ, (∀ d : ℕ, 0 < d → d < n →
      ((γ : GaloisField p n) ^ e) ^ (p ^ d - 1) ≠ 1) ∧ (γ : GaloisField p n) ^ e ≠ 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := (GaloisField p n)ˣ)
  have hord : orderOf γ = p ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_units,
      GaloisField.card p n (by omega)]
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hkey : ∀ m : ℕ, 0 < m → m ≤ e * (p ^ (n - 1) - 1) → (γ ^ m ≠ 1) := by
    intro m hm hle h1
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at hdvd
    have hle2 := Nat.le_of_dvd hm hdvd
    have hpn : p ^ n = p * p ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
    have hpos : 1 ≤ p ^ (n - 1) := Nat.one_le_pow _ _ hp.pos
    have h3u : 3 * p ^ (n - 1) ≤ p * p ^ (n - 1) := Nat.mul_le_mul_right _ hp3
    rw [hpn] at hle2
    generalize p * p ^ (n - 1) = v at hle2 h3u
    generalize p ^ (n - 1) = u at hpos h3u hle
    rcases he with rfl | rfl <;> omega
  refine ⟨γ, fun d hd hdn h1 => ?_, fun h1 => ?_⟩
  · apply hkey (e * (p ^ d - 1))
    · have : 1 < p ^ d := Nat.one_lt_pow (by omega) hp.one_lt
      rcases he with rfl | rfl <;> omega
    · have : p ^ d ≤ p ^ (n - 1) := Nat.pow_le_pow_right hp.pos (by omega)
      exact Nat.mul_le_mul_left _ (by omega)
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, pow_mul]
      exact h1
  · apply hkey e (by rcases he with rfl | rfl <;> omega)
    · have : 3 ≤ p ^ (n - 1) := (Nat.le_self_pow (by omega) p).trans' hp3
      generalize p ^ (n - 1) = u at this
      rcases he with rfl | rfl <;> omega
    · exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h1)

theorem mem_normalizer_centerOf {Y : Type} [Group Y] {T : Subgroup Y} {g : Y}
    (hg : g ∈ Subgroup.normalizer (T : Set Y)) :
    g ∈ Subgroup.normalizer (centerOf T : Set Y) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · rintro ⟨hxT, hxC⟩
    refine ⟨(hg x).mp hxT, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have hu' : g⁻¹ * u * g ∈ T := by
      have := (hg (g⁻¹ * u * g)).mpr (by simpa [mul_assoc] using hu)
      exact this
    have hc := Subgroup.mem_centralizer_iff.mp hxC _ hu'
    calc u * (g * x * g⁻¹) = g * ((g⁻¹ * u * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by rw [hc]
      _ = g * x * g⁻¹ * u := by group
  · rintro ⟨hxT, hxC⟩
    refine ⟨(hg x).mpr hxT, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have hu' : g * u * g⁻¹ ∈ T := (hg u).mp hu
    have hc := Subgroup.mem_centralizer_iff.mp hxC _ hu'
    have : g * (u * x) * g⁻¹ = g * (x * u) * g⁻¹ := by
      calc g * (u * x) * g⁻¹ = (g * u * g⁻¹) * (g * x * g⁻¹) := by group
        _ = (g * x * g⁻¹) * (g * u * g⁻¹) := hc
        _ = g * (x * u) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel this)

section Borel

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
  {Y₀ K : Subgroup Y}

theorem ReducedNongeneration.le_normalizer_of_borel_coatom (h : ReducedNongeneration p Y Rb Y₀)
    (hK : IsComponentOf K ⊤) (hnc : ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y))
    (hz : ∃ z ∈ (Rb : Subgroup Y), z ∉ K ∧ orderOf z = p ∧ z ∈ Subgroup.centralizer (K : Set Y))
    (T₁ : Sylow p K) (hT₁ : (T₁ : Subgroup K).map K.subtype = (Rb : Subgroup Y) ⊓ K)
    (hcoat : IsCoatom (Subgroup.normalizer ((T₁ : Subgroup K) : Set K))) :
    Y₀ ≤ Subgroup.normalizer ((((Rb : Subgroup Y) ⊓ K : Subgroup Y)) : Set Y) := by
  have hKn : K.Normal := h.normal_of_rankOne hK hnc
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hz
  obtain ⟨hN, hKY₀⟩ := h.rankOne_principle hK hnc hzR hzK hzp hzc
  have hT1 : (Rb : Subgroup Y) ⊓ K ≠ ⊥ := by
    intro hb; apply hnc; rw [hb]; infer_instance
  have hNT := hN _ le_rfl hT1
  have hUY₀ : (Rb : Subgroup Y) ⊓ K ≤ Y₀ := fun u hu =>
    hNT ⟨hu.2, Subgroup.le_normalizer hu⟩
  set W : Subgroup K := (Y₀ ⊓ K).subgroupOf K with hW
  have hNW : Subgroup.normalizer ((T₁ : Subgroup K) : Set K) ≤ W := by
    intro n hn
    have h1 := coe_mem_normalizer_map hn
    rw [hT₁] at h1
    exact Subgroup.mem_subgroupOf.mpr ⟨hNT h1, n.2⟩
  have hWtop : W ≠ ⊤ := by
    intro htop
    apply hKY₀
    intro k hk
    have : (⟨k, hk⟩ : K) ∈ W := htop ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp this).1
  have hWeq : W = Subgroup.normalizer ((T₁ : Subgroup K) : Set K) := by
    by_contra hne
    exact hWtop (hcoat.2 W (lt_of_le_of_ne hNW (Ne.symm hne)))
  have hY₀K : Y₀ ⊓ K ≤ Subgroup.normalizer ((((Rb : Subgroup Y) ⊓ K : Subgroup Y)) : Set Y) := by
    intro y hy
    have hyW : (⟨y, hy.2⟩ : K) ∈ W := Subgroup.mem_subgroupOf.mpr hy
    rw [hWeq] at hyW
    have h2 := (coe_mem_normalizer_map hyW).2
    rwa [hT₁] at h2
  exact le_normalizer_sylow_inf K Rb hUY₀ hY₀K

section NormalComponent

variable {L : Subgroup Y}

theorem centerOf_le_or_le_centralizer_of_torus [L.Normal] (hp2 : p ≠ 2) (Rb : Sylow p Y)
    (hnc : ¬ IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    (hNT : L ⊓ Subgroup.normalizer ((((Rb : Subgroup Y) ⊓ L : Subgroup Y)) : Set Y) ≤ Y₀)
    (hZL : Subgroup.center L = ⊥) (T₁ : Sylow p L)
    (hT₁ : (T₁ : Subgroup L).map L.subtype = (Rb : Subgroup Y) ⊓ L) (hF : OneLieFacts p L T₁)
    {n e : ℕ} (hTF : OneLieTorusFacts p L T₁ n e)
    (hY₀T : Y₀ ≤ Subgroup.normalizer ((((Rb : Subgroup Y) ⊓ L : Subgroup Y)) : Set Y))
    (W : Subgroup Y) (hWY₀ : W ≤ Y₀) (hY₀W : Y₀ ≤ Subgroup.normalizer (W : Set Y)) :
    centerOf ((Rb : Subgroup Y) ⊓ L) ≤ W ∨ W ≤ Subgroup.centralizer (L : Set Y) := by
  set T : Subgroup Y := (Rb : Subgroup Y) ⊓ L with hTdef
  set ZT : Subgroup Y := centerOf T with hZTdef
  have hT1 : T ≠ ⊥ := by intro hb; apply hnc; rw [hb]; infer_instance
  have hTY₀ : T ≤ Y₀ := fun u hu => hNT ⟨hu.2, Subgroup.le_normalizer hu⟩
  obtain ⟨ψK, hψinj, hψrange, hc⟩ := hTF.torus
  set ψ : Multiplicative (GaloisField p n) →* Y := L.subtype.comp ψK with hψdef
  have hψinj' : Function.Injective ψ := L.subtype_injective.comp hψinj
  have hψrange' : ψ.range = ZT := by
    rw [hψdef, MonoidHom.range_comp, hψrange, hZTdef, ← hT₁]
    exact map_subtype_centerOf _
  let φ : Multiplicative (GaloisField p n) ≃* ZT :=
    (MonoidHom.ofInjective hψinj').trans (MulEquiv.subgroupCongr hψrange')
  have hφ : ∀ a, (φ a : Y) = ψ a := fun a => rfl
  obtain ⟨γ, hγsub, hγ1⟩ := exists_gen_pow (n := n) hp2 hTF.two_le
    (hTF.e_cases.imp id (fun h => h.1))
  obtain ⟨c, hcN, hcact⟩ := hc γ
  have hcY : (c : Y) ∈ L ⊓ Subgroup.normalizer (T : Set Y) := by
    have := coe_mem_normalizer_map hcN
    rwa [hT₁] at this
  have hcY₀ : (c : Y) ∈ Y₀ := hNT hcY
  have hcφ : ∀ a, (c : Y) * (φ a : Y) * (c : Y)⁻¹ =
      φ (Multiplicative.ofAdd (((γ : GaloisField p n) ^ e) * Multiplicative.toAdd a)) := by
    intro a
    rw [hφ, hφ]
    simp only [hψdef, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_inv, ← Subgroup.coe_mul, hcact a]
  have hγ0 : ((γ : GaloisField p n) ^ e) ≠ 0 := pow_ne_zero _ γ.ne_zero
  by_cases hWT : W ⊓ T = ⊥
  ·
    right
    have hWCT : W ≤ Subgroup.centralizer (T : Set Y) := by
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h1 : w * u * w⁻¹ * u⁻¹ ∈ W := by
        have := (Subgroup.mem_normalizer_iff.mp (hY₀W (hTY₀ hu)) w⁻¹).mp (W.inv_mem hw)
        simpa only [mul_assoc] using W.mul_mem hw this
      have h2 : w * u * w⁻¹ * u⁻¹ ∈ T :=
        T.mul_mem ((Subgroup.mem_normalizer_iff.mp (hY₀T (hWY₀ hw)) u).mp hu) (T.inv_mem hu)
      have h3 : w * u * w⁻¹ * u⁻¹ ∈ W ⊓ T := ⟨h1, h2⟩
      rw [hWT, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
      exact h3.symm
    have hCT : Subgroup.centralizer (T : Set Y) ≤ T ⊔ Subgroup.centralizer (L : Set Y) := by
      rcases centralizer_le_sup_of_oneLieFacts hZL T₁ hF (V := T) (hT₁ ▸ le_rfl) hT1
          (fun x hx => by rw [← hT₁]; exact hx.2) with hle | ⟨hcen, hU⟩
      · rwa [hT₁] at hle
      · exfalso
        apply hTF.center_ne_of_unitary hU
        have h1 : ((T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L)).map
            L.subtype = (T₁ : Subgroup L).map L.subtype := by
          have := map_subtype_centerOf (T₁ : Subgroup L)
          rw [centerOf] at this
          rw [this, hT₁]
          rw [hT₁] at hcen
          exact hcen.symm
        exact Subgroup.map_injective L.subtype_injective h1
    intro w hw
    obtain ⟨a, haT, c', hc', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hCT (hWCT hw))
    have haZ : a ∈ ZT := by
      refine ⟨haT, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      have h1 := Subgroup.mem_centralizer_iff.mp (hWCT hw) u hu
      have h2 := Subgroup.mem_centralizer_iff.mp hc' u hu.2
      have : u * a * c' = a * u * c' := by
        calc u * a * c' = u * (a * c') := by group
          _ = (a * c') * u := h1
          _ = a * (c' * u) := by group
          _ = a * (u * c') := by rw [h2]
          _ = a * u * c' := by group
      exact mul_right_cancel this
    obtain ⟨x, hx⟩ : ∃ x, (φ x : Y) = a := ⟨φ.symm ⟨a, haZ⟩, by simp⟩
    have hcL : (c : Y) ∈ L := c.2
    have hcc' : (c : Y) * c' * (c : Y)⁻¹ = c' := by
      have := Subgroup.mem_centralizer_iff.mp hc' _ hcL
      rw [this]; group
    have hw' : (c : Y) * (a * c') * (c : Y)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hY₀W hcY₀) _).mp hw
    have hdiff : (c : Y) * a * (c : Y)⁻¹ * a⁻¹ ∈ W ⊓ T := by
      constructor
      · have h1 : (c : Y) * a * (c : Y)⁻¹ * a⁻¹ =
            ((c : Y) * (a * c') * (c : Y)⁻¹) * (a * c')⁻¹ := by
          calc (c : Y) * a * (c : Y)⁻¹ * a⁻¹
              = ((c : Y) * a * (c : Y)⁻¹) * ((c : Y) * c' * (c : Y)⁻¹) * c'⁻¹ * a⁻¹ := by
                rw [hcc']; group
            _ = _ := by group
        rw [h1]
        exact W.mul_mem hw' (W.inv_mem hw)
      · refine T.mul_mem ?_ (T.inv_mem haT)
        exact (Subgroup.mem_normalizer_iff.mp hcY.2 a).mp haT
    rw [hWT, Subgroup.mem_bot, mul_inv_eq_one] at hdiff
    rw [← hx, hcφ x] at hdiff
    have hx0 : x = 1 := by
      have h1 := φ.injective (Subtype.ext hdiff)
      have h2 := congrArg Multiplicative.toAdd h1
      simp only [toAdd_ofAdd] at h2
      have h3 : ((γ : GaloisField p n) ^ e - 1) * Multiplicative.toAdd x = 0 := by
        rw [sub_mul, h2, one_mul, sub_self]
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd (sub_eq_zero.mp h4) hγ1
      · exact h4
    rw [← hx, hx0, map_one, Subgroup.coe_one, one_mul]
    exact hc'
  ·
    left
    obtain ⟨x, hxWT, hx1⟩ := (W ⊓ T).bot_or_exists_ne_one.resolve_left hWT
    have hTp : IsPGroup p T := Rb.isPGroup'.to_le inf_le_left
    have : Group.IsNilpotent T := hTp.isNilpotent
    set H : Subgroup T := (W ⊓ T).subgroupOf T with hH
    have hHn : H.Normal := by
      refine ⟨fun y hy t => ?_⟩
      rw [hH, Subgroup.mem_subgroupOf] at hy ⊢
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hY₀W (hTY₀ t.2)) y).mp hy.1, ?_⟩
      exact T.mul_mem (T.mul_mem t.2 hy.2) (T.inv_mem t.2)
    have hH1 : H ≠ ⊥ := by
      intro hb
      have : (⟨x, hxWT.2⟩ : T) ∈ H := Subgroup.mem_subgroupOf.mpr hxWT
      rw [hb, Subgroup.mem_bot] at this
      exact hx1 (congrArg Subtype.val this)
    obtain ⟨y, ⟨hyH, hyC⟩, hy1⟩ :=
      (H ⊓ Subgroup.center T).bot_or_exists_ne_one.resolve_left
        (Group.IsNilpotent.inf_center_ne_bot_of_normal hH1)
    have hyW : (y : Y) ∈ W := (Subgroup.mem_subgroupOf.mp hyH).1
    have hyZ : (y : Y) ∈ ZT := by
      refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      have := Subgroup.mem_center_iff.mp hyC ⟨u, hu⟩
      exact congrArg Subtype.val this
    set Y' := W ⊓ ZT with hY'
    have hY'1 : Y' ≠ ⊥ := by
      intro hb
      have : (y : Y) ∈ Y' := ⟨hyW, hyZ⟩
      rw [hb, Subgroup.mem_bot] at this
      exact hy1 (Subtype.ext this)
    have hcY' : (c : Y) ∈ Subgroup.normalizer (Y' : Set Y) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hY₀W hcY₀, mem_normalizer_centerOf hcY.2⟩
    have hn0 : n ≠ 0 := by have := hTF.two_le; omega
    rcases eq_bot_or_eq_of_torus_conj' hn0 φ hγsub hγ0 hcφ (inf_le_right : Y' ≤ ZT) hcY' with
      hb | heq
    · exact absurd hb hY'1
    · rw [← heq]
      exact inf_le_left

end NormalComponent

theorem ReducedNongeneration.dichotomy_of_torus (h : ReducedNongeneration p Y Rb Y₀)
    (hK : IsComponentOf K ⊤) (hnc : ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y))
    (hz : ∃ z ∈ (Rb : Subgroup Y), z ∉ K ∧ orderOf z = p ∧ z ∈ Subgroup.centralizer (K : Set Y))
    (hZK : Subgroup.center K = ⊥) (T₁ : Sylow p K)
    (hT₁ : (T₁ : Subgroup K).map K.subtype = (Rb : Subgroup Y) ⊓ K) (hF : OneLieFacts p K T₁)
    {n e : ℕ} (hTF : OneLieTorusFacts p K T₁ n e)
    (hY₀T : Y₀ ≤ Subgroup.normalizer ((((Rb : Subgroup Y) ⊓ K : Subgroup Y)) : Set Y))
    (W : Subgroup Y) (hWY₀ : W ≤ Y₀) (hY₀W : Y₀ ≤ Subgroup.normalizer (W : Set Y)) :
    centerOf ((Rb : Subgroup Y) ⊓ K) ≤ W ∨ W ≤ Subgroup.centralizer (K : Set Y) := by
  have hKn : K.Normal := h.normal_of_rankOne hK hnc
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hz
  obtain ⟨hN, -⟩ := h.rankOne_principle hK hnc hzR hzK hzp hzc
  have hT1 : (Rb : Subgroup Y) ⊓ K ≠ ⊥ := by intro hb; apply hnc; rw [hb]; infer_instance
  exact centerOf_le_or_le_centralizer_of_torus h.ne_two Rb hnc (hN _ le_rfl hT1) hZK T₁ hT₁ hF hTF
    hY₀T W hWY₀ hY₀W

theorem le_centralizer_of_perfect_of_borel {n e : ℕ} [K.Normal] (T₁ : Sylow p K)
    (hT₁ : (T₁ : Subgroup K).map K.subtype = (Rb : Subgroup Y) ⊓ K)
    (hTF : OneLieTorusFacts p K T₁ n e)
    (hY₀T : Y₀ ≤ Subgroup.normalizer ((((Rb : Subgroup Y) ⊓ K : Subgroup Y)) : Set Y))
    {W : Subgroup Y} (hWY₀ : W ≤ Y₀) (hperf : ⁅W, W⁆ = W) :
    W ≤ Subgroup.centralizer (K : Set Y) := by
  set f : Y →* MulAut K := MulAut.conjNormal (H := K) with hf
  have hA : ∀ α ∈ W.map f, (T₁ : Subgroup K).map (α : K ≃* K).toMonoidHom = T₁ := by
    rintro _ ⟨w, hw, rfl⟩
    have hwN := hY₀T (hWY₀ hw)
    apply Subgroup.map_injective K.subtype_injective
    rw [hT₁]
    ext y
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      have hkT : (k : Y) ∈ (Rb : Subgroup Y) ⊓ K := hT₁ ▸ ⟨k, hk, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype, hf, MulAut.conjNormal_apply]
      exact (Subgroup.mem_normalizer_iff.mp hwN _).mp hkT
    · intro hy
      have hy' : w⁻¹ * y * w ∈ (Rb : Subgroup Y) ⊓ K := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hwN) y).mp hy
        simpa [mul_assoc] using this
      rw [← hT₁] at hy'
      obtain ⟨k, hk, hky⟩ := hy'
      refine ⟨_, ⟨k, hk, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype, hf, MulAut.conjNormal_apply]
      have hky' : (k : Y) = w⁻¹ * y * w := hky
      rw [hky']; group
  have hsolv := hTF.borel_solvable (W.map f) hA
  have hperf' : ⁅W.map f, W.map f⁆ = W.map f := by rw [← Subgroup.map_commutator, hperf]
  have hbot := eq_bot_of_commutator_eq_self_of_le le_rfl hsolv hperf'
  rw [Subgroup.map_eq_bot_iff, hf, ker_conjNormal_eq_centralizer] at hbot
  exact hbot

theorem pRank_top_le_of_aut {K : Subgroup Y} [K.Normal] {m : ℕ}
    (hC : ∀ A : Subgroup Y, A ≤ Subgroup.centralizer (K : Set Y) → IsPGroup p A → IsCyclic A)
    (haut : ∀ E : Subgroup (MulAut K), IsElemAbelian p E → Nat.card E ≤ p ^ m) :
    Open.pRank p (⊤ : Subgroup Y) ≤ m + 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨E, -, hE, hEcard⟩ := pRank_attained p hp (⊤ : Subgroup Y)
  set f : E →* MulAut K := (MulAut.conjNormal (H := K)).domRestrict E with hf
  have hker : Nat.card f.ker ≤ p := by
    let A : Subgroup Y := f.ker.map E.subtype
    have hAC : A ≤ Subgroup.centralizer (K : Set Y) := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : (MulAut.conjNormal (H := K)) (x : Y) = 1 := hx
      have h2 : (x : Y) ∈ (MulAut.conjNormal (H := K)).ker := h1
      rwa [ker_conjNormal_eq_centralizer] at h2
    have hAp : ∀ a ∈ A, a ^ p = 1 := by
      rintro _ ⟨x, -, rfl⟩
      exact hE.2 x x.2
    have hApg : IsPGroup p A := fun a => ⟨1, Subtype.ext (by simpa using hAp a a.2)⟩
    have hcyc := hC A hAC hApg
    have hcardA : Nat.card A = Nat.card f.ker :=
      Nat.card_congr (f.ker.equivMapOfInjective E.subtype E.subtype_injective).toEquiv.symm
    rw [← hcardA]
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hgp : g ^ p = 1 := Subtype.ext (by simpa using hAp (g : Y) g.2)
    have hord : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact Nat.le_of_dvd hp.pos hord
  have hrange : Nat.card f.range ≤ p ^ m := by
    rw [hf, MonoidHom.domRestrict_range]
    exact haut _ (elementary_abelian_map p hE _)
  have hsplit : Nat.card E = Nat.card f.ker * Nat.card f.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hle : p ^ Open.pRank p (⊤ : Subgroup Y) ≤ p ^ (m + 1) := by
    rw [← hEcard, hsplit, pow_succ, mul_comm]
    exact Nat.mul_le_mul hrange hker
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle

end Borel

theorem stmtOneLieBorel :
    ∀ {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime] (Rb : Sylow p Y) (Y₀ K : Subgroup Y)
      (n e : ℕ), ReducedNongeneration p Y Rb Y₀ → IsComponentOf K ⊤ →
      ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) →
      (∃ z ∈ (Rb : Subgroup Y), z ∉ K ∧ orderOf z = p ∧ z ∈ Subgroup.centralizer (K : Set Y)) →
      Subgroup.center K = ⊥ →
      ∀ T₁ : Sylow p K, (T₁ : Subgroup K).map K.subtype = (Rb : Subgroup Y) ⊓ K →
      OneLieFacts p K T₁ → OneLieTorusFacts p K T₁ n e →
      Y₀ ≤ Subgroup.normalizer ((((Rb : Subgroup Y) ⊓ K : Subgroup Y)) : Set Y) ∧
      (∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) →
        centerOf ((Rb : Subgroup Y) ⊓ K) ≤ W ∨ W ≤ Subgroup.centralizer (K : Set Y)) ∧
      (∀ W : Subgroup Y, W ≤ Y₀ → ⁅W, W⁆ = W → W ≤ Subgroup.centralizer (K : Set Y)) ∧
      Open.pRank p (⊤ : Subgroup Y) ≤ (if e = 2 then n else 2 * n) + 1 := by
  intro Y _ _ p _ Rb Y₀ K n e h hK hnc hz hZK T₁ hT₁ hF hTF
  have hKn : K.Normal := h.normal_of_rankOne hK hnc
  have hY₀T := h.le_normalizer_of_borel_coatom hK hnc hz T₁ hT₁ hTF.borel_coatom
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hz
  obtain ⟨-, hKY₀⟩ := h.rankOne_principle hK hnc hzR hzK hzp hzc
  refine ⟨hY₀T, fun W hWY₀ hY₀W => ?_, fun W hWY₀ hperf => ?_, ?_⟩
  · exact h.dichotomy_of_torus hK hnc ⟨z, hzR, hzK, hzp, hzc⟩ hZK T₁ hT₁ hF hTF hY₀T W hWY₀ hY₀W
  · exact le_centralizer_of_perfect_of_borel T₁ hT₁ hTF hY₀T hWY₀ hperf
  · refine pRank_top_le_of_aut (K := K) (fun A hA hAp => ?_) hTF.autRank
    exact h.isCyclic_of_le_centralizer hK hKY₀ hAp hA

end CFSG.AGLEmbedding
