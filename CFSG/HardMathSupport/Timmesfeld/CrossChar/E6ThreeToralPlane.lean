module

public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21
public import CFSG.LieType.Chevalley.GraphFixedF4Canonical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint.Chevalley

section General

variable {S Q : Type*} [Group S] [Group Q]

@[expose] def commKerHom (π : S →* Q) (hker : π.ker ≤ Subgroup.center S) {D : Subgroup Q}
    (hD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (g : D.comap π) : D.comap π →* π.ker :=
  MonoidHom.mk' (fun u => ⟨(g : S) * (u : S) * (g : S)⁻¹ * (u : S)⁻¹, by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
        hD _ g.2 _ u.2]
      group⟩)
    fun u v => by
      apply Subtype.ext
      have hcv : (g : S) * (v : S) * (g : S)⁻¹ * (v : S)⁻¹ ∈ Subgroup.center S := hker (by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hD _ g.2 _ v.2]
        group)
      have hc := Subgroup.mem_center_iff.1 hcv
      change (g : S) * ((u : S) * (v : S)) * (g : S)⁻¹ * ((u : S) * (v : S))⁻¹ =
        ((g : S) * (u : S) * (g : S)⁻¹ * (u : S)⁻¹) * ((g : S) * (v : S) * (g : S)⁻¹ * (v : S)⁻¹)
      calc (g : S) * ((u : S) * (v : S)) * (g : S)⁻¹ * ((u : S) * (v : S))⁻¹
          = (g : S) * u * ((g : S)⁻¹ * ((g : S) * v * (g : S)⁻¹ * (v : S)⁻¹)) * (u : S)⁻¹ := by
            group
        _ = (g : S) * u * (g : S)⁻¹ * (((g : S) * v * (g : S)⁻¹ * (v : S)⁻¹) * (u : S)⁻¹) := by
            group
        _ = (g : S) * u * (g : S)⁻¹ * ((u : S)⁻¹ * ((g : S) * v * (g : S)⁻¹ * (v : S)⁻¹)) := by
            rw [hc (u : S)⁻¹]
        _ = ((g : S) * u * (g : S)⁻¹ * (u : S)⁻¹) * ((g : S) * v * (g : S)⁻¹ * (v : S)⁻¹) := by
            group

theorem coe_commKerHom (π : S →* Q) (hker : π.ker ≤ Subgroup.center S) {D : Subgroup Q}
    (hD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (g u : D.comap π) :
    ((commKerHom π hker hD g u : π.ker) : S) = (g : S) * (u : S) * (g : S)⁻¹ * (u : S)⁻¹ :=
  rfl

theorem commute_of_mem_closure_pair {a b : S} (hab : a * b = b * a) {u v : S}
    (hu : u ∈ Subgroup.closure ({a, b} : Set S)) (hv : v ∈ Subgroup.closure ({a, b} : Set S)) :
    u * v = v * u := by
  have hs : ({a, b} : Set S) ⊆ Subgroup.centralizer ({a, b} : Set S) := by
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro t ht
    rcases hs with rfl | hs <;> rcases ht with rfl | ht
    · rfl
    · rw [Set.mem_singleton_iff.1 ht]; exact hab.symm
    · rw [Set.mem_singleton_iff.1 hs]; exact hab
    · rw [Set.mem_singleton_iff.1 hs, Set.mem_singleton_iff.1 ht]
  have h1 : Subgroup.closure ({a, b} : Set S) ≤ Subgroup.centralizer ({a, b} : Set S) :=
    (Subgroup.closure_le _).2 hs
  have h2 := Subgroup.closure_le_centralizer_centralizer ({a, b} : Set S)
  exact Subgroup.mem_centralizer_iff.1 (h2 hv) u (h1 hu)

theorem exists_le_comap_commute_of_ker_dvd_three (π : S →* Q)
    (hker : π.ker ≤ Subgroup.center S) (hker3 : Nat.card π.ker ∣ 3) {D : Subgroup Q}
    (hDπ : D ≤ π.range) (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 3 ^ 3) :
    ∃ E : Subgroup Q, E ≤ D ∧ 3 ^ 2 ≤ Nat.card E ∧
      ∀ x ∈ E.comap π, ∀ y ∈ E.comap π, x * y = y * x := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  by_cases hab : ∀ x ∈ D.comap π, ∀ y ∈ D.comap π, x * y = y * x
  · exact ⟨D, le_rfl, by rw [hcard]; norm_num, hab⟩
  push Not at hab
  obtain ⟨x, hx, y, hy, hxy⟩ := hab
  set x' : D.comap π := ⟨x, hx⟩
  set y' : D.comap π := ⟨y, hy⟩
  set ρ : D.comap π →* D := ((π.comp (D.comap π).subtype).codRestrict D fun u => u.2) with hρ
  have hρs : Function.Surjective ρ := by
    rintro ⟨d, hd⟩
    obtain ⟨s, hs⟩ := hDπ hd
    exact ⟨⟨s, by change π s ∈ D; rw [hs]; exact hd⟩, Subtype.ext hs⟩
  set fx := commKerHom π hker hDc x'
  set fy := commKerHom π hker hDc y'
  set N := fx.ker ⊓ fy.ker with hN
  have hkerfin : Finite π.ker := Nat.finite_of_card_ne_zero fun h => by
    rw [h] at hker3
    exact absurd (Nat.eq_zero_of_zero_dvd hker3) (by norm_num)
  have hidx : ∀ f : D.comap π →* π.ker, f.ker.index ≤ 3 := fun f => by
    rw [Subgroup.index_ker]
    exact (Subgroup.card_le_card_group f.range).trans (Nat.le_of_dvd (by norm_num) hker3)
  have hidx0 : ∀ f : D.comap π →* π.ker, f.ker.index ≠ 0 := fun f => by
    rw [Subgroup.index_ker]
    exact Nat.card_pos.ne'
  have hNidx : N.index ≤ 9 :=
    Subgroup.index_inf_le.trans (by nlinarith [hidx fx, hidx fy])
  have hNidx0 : N.index ≠ 0 := Subgroup.index_inf_ne_zero (hidx0 fx) (hidx0 fy)
  set Nbar := N.map ρ with hNbar
  have hNbidx : Nbar.index ∣ N.index := Subgroup.index_map_dvd N hρs
  have hNb : Nat.card Nbar * Nbar.index = 27 := by
    rw [Subgroup.card_mul_index, hcard]
    norm_num
  have hNb3 : 3 ≤ Nat.card Nbar := by
    have h1 : Nbar.index ≤ 9 :=
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hNidx0) hNbidx).trans hNidx
    have h2 : 0 < Nat.card Nbar := Nat.card_pos
    nlinarith
  obtain ⟨r, hr, hr1⟩ : ∃ r ∈ Nbar, r ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nbar = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [this, Subgroup.card_bot] at hNb3
    omega
  obtain ⟨rt, hrt, hrtr⟩ := Subgroup.mem_map.1 hr
  have hrtx : x * (rt : S) = rt * x := by
    have h1 := congrArg Subtype.val (MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hrt).1)
    rw [coe_commKerHom] at h1
    change x * (rt : S) * x⁻¹ * (rt : S)⁻¹ = 1 at h1
    calc x * (rt : S) = (x * (rt : S) * x⁻¹ * (rt : S)⁻¹) * ((rt : S) * x) := by group
      _ = rt * x := by rw [h1, one_mul]
  set w : π.ker := fy x' with hw
  have hw1 : w ≠ 1 := by
    intro h
    apply hxy
    have h1 := congrArg Subtype.val h
    rw [hw, coe_commKerHom] at h1
    change y * x * y⁻¹ * x⁻¹ = 1 at h1
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by
        have h2 : x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group
        rw [h2, h1, inv_one, one_mul]
  have hwo : orderOf w = 3 := by
    have h1 := orderOf_dvd_natCard w
    have h2 : orderOf w ∣ 3 := h1.trans hker3
    rcases (Nat.dvd_prime Nat.prime_three).1 h2 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hw1
    · exact h
  set E : Subgroup Q := (Subgroup.closure ({(rt : S), x} : Set S)).map π with hE
  have hclD : Subgroup.closure ({(rt : S), x} : Set S) ≤ D.comap π := by
    refine (Subgroup.closure_le _).2 ?_
    rintro s (rfl | hs)
    · exact rt.2
    · rw [Set.mem_singleton_iff.1 hs]; exact hx
  have hED : E ≤ D := (Subgroup.map_mono hclD).trans (Subgroup.map_comap_le _ _)
  refine ⟨E, hED, ?_, ?_⟩
  ·
    have hxE : π x ∈ E := Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (by simp))
    have hrE : π rt ∈ E := Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (by simp))
    have hπrt : π rt = (r : Q) := by rw [← hrtr]; rfl
    have hx3 : π x ^ 3 = 1 := hD.2 _ hx
    have hx1 : π x ≠ 1 := by
      intro h
      apply hxy
      have hxc := Subgroup.mem_center_iff.1 (hker (MonoidHom.mem_ker.2 h))
      exact (hxc y).symm
    have hnot : π rt ∉ Subgroup.zpowers (π x) := by
      rintro ⟨n, hn⟩
      change π x ^ n = π rt at hn
      set z : S := (((x' ^ n)⁻¹ * rt : D.comap π) : S) with hzdef
      have hz : z ∈ π.ker := by
        rw [MonoidHom.mem_ker, hzdef, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow,
          map_mul, map_inv, map_zpow, hn, inv_mul_cancel]
      have hc := Subgroup.mem_center_iff.1 (hker hz)
      have hk : (x' ^ n)⁻¹ * rt ∈ fy.ker := by
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        rw [coe_commKerHom]
        change y * z * y⁻¹ * z⁻¹ = 1
        rw [hc y]
        group
      have hfy : fy (x' ^ n) = fy rt := by
        have h1 := MonoidHom.mem_ker.1 hk
        rw [map_mul, map_inv, inv_mul_eq_one] at h1
        exact h1
      have hrt1 : fy rt = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hrt).2
      rw [hrt1, map_zpow] at hfy
      have h3 : ((orderOf w : ℕ) : ℤ) ∣ n := orderOf_dvd_iff_zpow_eq_one.2 hfy
      rw [hwo] at h3
      obtain ⟨m, rfl⟩ := h3
      apply hr1
      apply Subtype.ext
      rw [Subgroup.coe_one, ← hπrt, ← hn, zpow_mul, zpow_natCast, hx3, one_zpow]
    have hlt : Subgroup.zpowers (π x) < E := by
      refine lt_of_le_of_ne ((Subgroup.zpowers_le).2 hxE) fun h => hnot ?_
      rw [h]
      exact hrE
    have : Finite E := Finite.of_injective (Subgroup.inclusion hED)
      (Subgroup.inclusion_injective hED)
    have hcardx : Nat.card (Subgroup.zpowers (π x)) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime hx3 hx1
    have hlt' := Subgroup.card_lt_of_lt hlt
    have hdvd : Nat.card E ∣ 3 ^ 3 := hcard ▸ Subgroup.card_dvd_of_le hED
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    rw [hk] at hlt' ⊢
    rw [hcardx] at hlt'
    have hk2 : 2 ≤ k := by
      by_contra hk2
      interval_cases k <;> simp at hlt'
    exact Nat.pow_le_pow_right (by norm_num) hk2
  ·
    intro a ha b hb
    rw [hE, Subgroup.comap_map_eq] at ha hb
    rw [← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul] at ha hb
    obtain ⟨a₁, ha₁, k₁, hk₁, rfl⟩ := ha
    obtain ⟨b₁, hb₁, k₂, hk₂, rfl⟩ := hb
    have hc₁ := Subgroup.mem_center_iff.1 (hker hk₁)
    have hc₂ := Subgroup.mem_center_iff.1 (hker hk₂)
    have hab₁ := commute_of_mem_closure_pair hrtx.symm ha₁ hb₁
    exact (Commute.mul_left (Commute.mul_right hab₁ (hc₂ a₁)) (hc₁ (b₁ * k₂)).symm).eq

end General

section E6

open CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Chevalley


@[expose] noncomputable def e6InnIsogeny (K : Type) [Field K] [Finite K] :
    ↥(e6Data_valid.minGroup K) →* MulAut (adjointGroup Tag.E6 K) :=
  (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).comp (e6Isogeny K)

theorem range_e6InnIsogeny (K : Type) [Field K] [Finite K] :
    (e6InnIsogeny K).range = innerAut (adjointGroup Tag.E6 K) := by
  rw [e6InnIsogeny, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (e6Isogeny_surjective K),
    Subgroup.map_top]
  rfl

theorem ker_e6InnIsogeny (K : Type) [Field K] [Finite K] :
    (e6InnIsogeny K).ker = Subgroup.center ↥(e6Data_valid.minGroup K) := by
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  have hinj := mulAut_conj_injective_of_center_eq_bot
    (center_adjointGroup_eq_bot (τ := Tag.E6) (K := K))
  rw [e6InnIsogeny, MonoidHom.ker_comp_of_injective _ _ hinj,
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center]

theorem exists_isotropic_plane_E6 (K : Type) [Field K] [Finite K]
    {D : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hDin : D ≤ innerAut (adjointGroup Tag.E6 K))
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 3 ^ 3) :
    ∃ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), E ≤ D ∧ 3 ^ 2 ≤ Nat.card E ∧
      ∀ x ∈ E.comap (e6InnIsogeny K), ∀ y ∈ E.comap (e6InnIsogeny K), x * y = y * x := by
  refine exists_le_comap_commute_of_ker_dvd_three (e6InnIsogeny K) ?_ ?_
    (by rw [range_e6InnIsogeny]; exact hDin) hD hcard
  · rw [ker_e6InnIsogeny]
  · rw [ker_e6InnIsogeny, (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 K).1]
    exact Nat.gcd_dvd_left 3 _

end E6

end CFSG.HardMathSupport.Timmesfeld.CrossChar
