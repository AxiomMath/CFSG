module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15Common
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15OuterGen

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.Open CFSG.Quasithin

section Generic

variable {G : Type} [Group G]

theorem exists_e_of_four [Finite G] {E : Subgroup G} (hE4 : IsFourSubgroup E) {z : G} (hz : z ∈ E)
    (hz1 : z ≠ 1) :
    ∃ e ∈ E, e ≠ 1 ∧ e ≠ z ∧ e * e = 1 ∧ e * z = z * e ∧ E = Subgroup.closure {z, e} := by
  obtain ⟨e, heE, he⟩ : ∃ e ∈ E, e ≠ 1 ∧ e ≠ z := by
    by_contra h'
    push Not at h'
    have h2 : Nat.card E ≤ 2 := card_le_two_of_forall_eq (a := z) fun b hb => by
      by_cases hb1 : b = 1
      · exact Or.inl hb1
      · exact Or.inr (h' b hb hb1)
    have := hE4.2
    omega
  have hee : e * e = 1 := by
    have := hE4.1.2 e heE
    rwa [sq] at this
  have hzz : z * z = 1 := by
    have := hE4.1.2 z hz
    rwa [sq] at this
  have hcomm : e * z = z * e := isElemAbelian_mul_comm hE4.1 heE hz
  refine ⟨e, heE, he.1, he.2, hee, hcomm, ?_⟩
  have hle : Subgroup.closure ({z, e} : Set G) ≤ E := by
    rw [Subgroup.closure_le]
    intro v hv
    rcases hv with rfl | hv
    · exact hz
    · rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact heE
  have hcard : Nat.card ↥(Subgroup.closure ({z, e} : Set G)) = 4 :=
    card_closure_pair hzz hee hcomm.symm hz1 he.1 he.2.symm
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hE4.2])).symm

theorem conj_mem_centSKz {S K : Subgroup G} {zK x' r : G}
    (hx' : x' ∈ Subgroup.normalizer (S : Set G))
    (hx'c : ∀ v ∈ threeCoreCent K zK, x' * v = v * x') (hr : r ∈ centSKz S K zK) :
    x'⁻¹ * r * x' ∈ centSKz S K zK := by
  rw [mem_centSKz_iff] at hr ⊢
  refine ⟨?_, fun v hv => ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx') r).mp hr.1
    simpa using this
  · have hxv : x' * v = v * x' := hx'c v hv
    have hxv' : x'⁻¹ * v = v * x'⁻¹ := by
      calc x'⁻¹ * v = x'⁻¹ * (v * x') * x'⁻¹ := by group
        _ = x'⁻¹ * (x' * v) * x'⁻¹ := by rw [hxv]
        _ = v * x'⁻¹ := by group
    have hrv := hr.2 v hv
    calc v * (x'⁻¹ * r * x') = (v * x'⁻¹) * r * x' := by group
      _ = (x'⁻¹ * v) * r * x' := by rw [← hxv']
      _ = x'⁻¹ * (v * r) * x' := by group
      _ = x'⁻¹ * (r * v) * x' := by rw [hrv]
      _ = x'⁻¹ * r * (v * x') := by group
      _ = x'⁻¹ * r * (x' * v) := by rw [← hxv]
      _ = (x'⁻¹ * r * x') * v := by group

end Generic

section Config

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  (N : Notation25 hs) {t zK : G}

theorem centralizer_inf_eq_zpowers (h : Lv2513 N t zK) (F : K33Facts N.K)
    (hKt : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N.K : Set G))
    (hSC : N.SC = Subgroup.zpowers t) :
    Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K : Set G) =
      Subgroup.zpowers t := by
  have hf := h.facts2511
  have hKH := H_le_normalizer_K N h F
  have hK0 := N.K0_eq hKH
  have hzKK := zK_mem_K N h F
  obtain ⟨hzz, -⟩ := z_eq_zK N h F hKt
  have hzK' : N.z ∈ N.K := hzz ▸ hzKK
  have htK : ∀ k ∈ N.K, k * t = t * k := fun k hk =>
    Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer hf.t_mem) k (N.K_le_K0 hk)
  set Gt := Subgroup.centralizer ({t} : Set G) with hGt
  set C₁ := Gt ⊓ Subgroup.centralizer (N.K : Set G) with hC₁
  have htC₁ : t ∈ C₁ := ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl,
    Subgroup.mem_centralizer_iff.mpr fun k hk => htK k hk⟩
  have hCX : C₁ ≤ Gt := inf_le_left
  have hnorm : ∀ g' ∈ Gt, ∀ c ∈ C₁, g' * c * g'⁻¹ ∈ C₁ := by
    intro g' hg' c hc
    have hg'N : g' ∈ Subgroup.normalizer (N.K : Set G) := hKt hg'
    refine ⟨Gt.mul_mem (Gt.mul_mem hg' hc.1) (Gt.inv_mem hg'),
      Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
    have hk' : g'⁻¹ * k * g' ∈ N.K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg'N) k).mp hk
      simpa using this
    have hck := Subgroup.mem_centralizer_iff.mp hc.2 _ hk'
    calc k * (g' * c * g'⁻¹) = g' * ((g'⁻¹ * k * g') * c) * g'⁻¹ := by group
      _ = g' * (c * (g'⁻¹ * k * g')) * g'⁻¹ := by rw [hck]
      _ = (g' * c * g'⁻¹) * k := by group
  have hXC : Gt ≤ Subgroup.normalizer (C₁ : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact hnorm g hg c hc
    · intro hc
      have := hnorm g⁻¹ (Gt.inv_mem hg) _ hc
      simpa [mul_assoc] using this
  have hSC' : N.S ⊓ C₁ = Subgroup.zpowers t := by
    rw [← hSC]
    ext s
    constructor
    · rintro ⟨hsS, -, hsC⟩
      refine ⟨hsS, ?_⟩
      rw [hK0]
      exact hsC
    · rintro ⟨hsS, hsC⟩
      rw [hK0] at hsC
      exact ⟨hsS, hf.H_le (N.S_le_H hsS), hsC⟩
  obtain ⟨O, hOC, hXO, hOodd, hCO⟩ :=
    exists_odd_normalized_of_two hf.sylow hCX hXC htC₁ hf.t_sq hf.t_ne_one hSC'
  have hΓ : IsGamma M Gt := hf.gammaU.isGamma
  obtain ⟨htup, -⟩ := N.tuple_of_overgroup hΓ hf.H_le
  have hOle : O ≤ oddCoreIn Gt := le_oddCoreIn' (hOC.trans hCX) hXO hOodd
  have hO1 : O = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    have hinv := htup.z_inverts_oddCoreIn hs y (hOle hy)
    have hyC : y ∈ C₁ := hOC hy
    have hcomm : N.z * y = y * N.z := Subgroup.mem_centralizer_iff.mp hyC.2 N.z hzK'
    have h1 : N.z⁻¹ * y * N.z = y := by
      calc N.z⁻¹ * y * N.z = N.z⁻¹ * (y * N.z) := by group
        _ = N.z⁻¹ * (N.z * y) := by rw [hcomm]
        _ = y := by group
    rw [h1] at hinv
    have hy2 : y * y = 1 := mul_eq_one_iff_eq_inv.mpr hinv
    have hord : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hy2)
    have hodd : Odd (orderOf y) := by
      have h3 : orderOf (⟨y, hy⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h3
      exact Odd.of_dvd_nat hOodd h3
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h2 | h2
    · exact orderOf_eq_one_iff.mp h2
    · rw [h2] at hodd
      exact absurd hodd (by decide)
  have hcard : Nat.card C₁ = 2 := by
    rw [hCO, hO1]
    simp
  symm
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr htC₁)
  rw [hcard, Nat.card_zpowers, orderOf_eq_prime hf.t_sq hf.t_ne_one]

theorem Gt_decomp (h : Lv2513 N t zK) (F : K33Facts N.K) (L : L33Facts N.K)
    (hKt : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N.K : Set G))
    (hSC : N.SC = Subgroup.zpowers t) {y : G} (hyS : y ∈ N.S) (hyo : ¬ Ch1.InducesInner y N.K) :
    ∀ g ∈ Subgroup.centralizer ({t} : Set G),
      ∃ c ∈ Subgroup.zpowers t, ∃ a ∈ N.K ⊔ Subgroup.zpowers y, g = c * a := by
  have hf := h.facts2511
  have hKH := H_le_normalizer_K N h F
  have hsimple : IsSimpleGroup ↥N.K := h.facts258.simple
  have hZK : ∀ x ∈ N.K, (∀ w ∈ N.K, x * w = w * x) → x = 1 := fun x hx hc =>
    N.center_K_trivial hsimple hx hc
  have hC₁ := centralizer_inf_eq_zpowers N h F hKt hSC
  set Gt := Subgroup.centralizer ({t} : Set G) with hGt
  have hKGt : N.K ≤ Gt := N.K_le_H.trans hf.H_le
  have inner_case : ∀ g' ∈ Gt, Ch1.InducesInner g' N.K →
      ∃ c ∈ Subgroup.zpowers t, ∃ l ∈ N.K, g' = c * l := by
    intro g' hg' hin
    obtain ⟨l, hl, hact⟩ := hin
    have hcent : g' * l⁻¹ ∈ Subgroup.centralizer (N.K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := hact x hx
      calc x * (g' * l⁻¹) = g' * (g'⁻¹ * x * g') * l⁻¹ := by group
        _ = g' * (l⁻¹ * x * l) * l⁻¹ := by rw [h1]
        _ = (g' * l⁻¹) * x := by group
    have hmem : g' * l⁻¹ ∈ Gt ⊓ Subgroup.centralizer (N.K : Set G) :=
      ⟨Gt.mul_mem hg' (Gt.inv_mem (hKGt hl)), hcent⟩
    rw [hC₁] at hmem
    exact ⟨g' * l⁻¹, hmem, l, hl, by group⟩
  intro g hg
  have hgN : g ∈ Subgroup.normalizer (N.K : Set G) := hKt hg
  by_cases hin : Ch1.InducesInner g N.K
  · obtain ⟨c, hc, l, hl, rfl⟩ := inner_case g hg hin
    exact ⟨c, hc, l, Subgroup.mem_sup_left hl, rfl⟩
  · have hyN : y ∈ Subgroup.normalizer (N.K : Set G) := N.S_le_normalizer_K hKH hyS
    have hin' := inducesInner_inv_mul_of_not L.aut_card hZK hyN hgN hyo hin
    have hyGt : y ∈ Gt := hf.H_le (N.S_le_H hyS)
    obtain ⟨c, hc, l, hl, hcl⟩ :=
      inner_case (y⁻¹ * g) (Gt.mul_mem (Gt.inv_mem hyGt) hg) hin'
    have hyc : y * c = c * y := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      exact (Commute.zpow_right (show Commute y t from
        Subgroup.mem_centralizer_singleton_iff.mp hyGt) m).eq
    refine ⟨c, hc, y * l, Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
      (Subgroup.mem_sup_left hl), ?_⟩
    calc g = y * (y⁻¹ * g) := by group
      _ = y * (c * l) := by rw [hcl]
      _ = c * (y * l) := by rw [← mul_assoc, hyc, mul_assoc]

end Config

end CFSG.QuasithinUnique.Unc25K1
