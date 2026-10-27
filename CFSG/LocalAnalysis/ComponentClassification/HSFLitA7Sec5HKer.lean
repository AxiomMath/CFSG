module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec5HAct

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Sec8

namespace Sec5H

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

@[expose] def M (D : S.Sec5 F T₁) : Subgroup X where
  carrier := {n | n ∈ normalizer (D.T₂ : Set X) ∧
    ∃ τ ∈ D.T₂, ∀ a ∈ D.T₂, n * a * n⁻¹ = τ * a * τ⁻¹}
  mul_mem' := by
    rintro n m ⟨hn, τ, hτ, hnτ⟩ ⟨hm, σ, hσ, hmσ⟩
    refine ⟨mul_mem hn hm, τ * σ, mul_mem hτ hσ, fun a ha => ?_⟩
    have hma : m * a * m⁻¹ ∈ D.T₂ := (mem_normalizer_iff.mp hm a).mp ha
    calc n * m * a * (n * m)⁻¹ = n * (m * a * m⁻¹) * n⁻¹ := by group
      _ = τ * (σ * a * σ⁻¹) * τ⁻¹ := by rw [hnτ _ hma, hmσ a ha]
      _ = τ * σ * a * (τ * σ)⁻¹ := by group
  one_mem' := ⟨one_mem _, 1, one_mem _, fun a _ => by group⟩
  inv_mem' := by
    rintro n ⟨hn, τ, hτ, hnτ⟩
    refine ⟨inv_mem hn, τ⁻¹, inv_mem hτ, fun a ha => ?_⟩
    have hb : n⁻¹ * a * n⁻¹⁻¹ ∈ D.T₂ := (mem_normalizer_iff.mp (inv_mem hn) a).mp ha
    have h := hnτ _ hb
    have h2 : n * (n⁻¹ * a * n⁻¹⁻¹) * n⁻¹ = a := by group
    rw [h2] at h
    calc n⁻¹ * a * n⁻¹⁻¹ = τ⁻¹ * (τ * (n⁻¹ * a * n⁻¹⁻¹) * τ⁻¹) * τ := by group
      _ = τ⁻¹ * a * τ⁻¹⁻¹ := by rw [← h]; group

theorem T₂_le_M (D : S.Sec5 F T₁) : D.T₂ ≤ M D :=
  fun τ hτ => ⟨le_normalizer hτ, τ, hτ, fun _ _ => rfl⟩

theorem conj_mem_M (D : S.Sec5 F T₁) {n m : X} (hn : n ∈ normalizer (D.T₂ : Set X))
    (hm : m ∈ M D) : n * m * n⁻¹ ∈ M D := by
  obtain ⟨hmN, τ, hτ, hmτ⟩ := hm
  refine ⟨mul_mem (mul_mem hn hmN) (inv_mem hn), n * τ * n⁻¹,
    (mem_normalizer_iff.mp hn τ).mp hτ, fun a ha => ?_⟩
  have hb : n⁻¹ * a * n⁻¹⁻¹ ∈ D.T₂ := (mem_normalizer_iff.mp (inv_mem hn) a).mp ha
  calc n * m * n⁻¹ * a * (n * m * n⁻¹)⁻¹ = n * (m * (n⁻¹ * a * n⁻¹⁻¹) * m⁻¹) * n⁻¹ := by group
    _ = n * (τ * (n⁻¹ * a * n⁻¹⁻¹) * τ⁻¹) * n⁻¹ := by rw [hmτ _ hb]
    _ = n * τ * n⁻¹ * a * (n * τ * n⁻¹)⁻¹ := by group

omit [Finite X] in
theorem conjSub_eq_of_acts {n τ : X} {H K : Subgroup X} (hH : H ≤ K)
    (hnτ : ∀ a ∈ K, n * a * n⁻¹ = τ * a * τ⁻¹) : conjSub n H = conjSub τ H := by
  ext f
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, (hnτ a (hH ha)).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, hnτ a (hH ha)⟩

namespace Setup

variable {D : S.Sec5 F T₁} (C : Setup D)

@[expose] noncomputable def Olist : List X := [S.t, S.t * S.z, S.t * F.yF, S.t * S.z * F.yF]

theorem Olist_eq : Olist (S := S) (F := F) = [RH.t, RH.t * RH.z, RH.t * RH.y,
    RH.t * RH.z * RH.y].map C.ι := by
  simp [Olist, map_mul, C.ι_t, C.ι_z, C.ι_y]

theorem mem_Olist {e : X} : e ∈ Olist (S := S) (F := F) ↔
    ∃ c ∈ [RH.t, RH.t * RH.z, RH.t * RH.y, RH.t * RH.z * RH.y], C.ι c = e := by
  rw [C.Olist_eq, List.mem_map]

include C in
theorem T₂_conj_O {τ e : X} (hτ : τ ∈ D.T₂) (he : e ∈ Olist (S := S) (F := F)) :
    τ * e * τ⁻¹ = e ∨ τ * e * τ⁻¹ = S.z * e := by
  obtain ⟨τ', hτ', rfl⟩ := C.mem_T₂.mp hτ
  obtain ⟨c, hc, rfl⟩ := C.mem_Olist.mp he
  rw [← C.ι_z, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  exact (RH.T2_orbit_O τ' hτ' c hc).imp (congrArg C.ι) (congrArg C.ι)

include C in
theorem O_facts {e : X} (he : e ∈ Olist (S := S) (F := F)) : e * e = 1 ∧ e * S.z = S.z * e := by
  obtain ⟨c, hc, rfl⟩ := C.mem_Olist.mp he
  obtain ⟨h1, h2⟩ := RH.O_facts c hc
  rw [← C.ι_z, ← map_mul, h1, map_one, ← map_mul, h2, map_mul]
  exact ⟨rfl, rfl⟩

include C in
theorem mem_closure_zy {f : X} (hf : f ∈ closure ({S.z, F.yF} : Set X)) :
    f = 1 ∨ f = S.z ∨ f = F.yF ∨ f = S.z * F.yF := by
  have heq : closure ({S.z, F.yF} : Set X) = RH.ZY.map C.ι := by
    rw [RH.ZY, map_span]
    congr 1
    ext g
    simp [C.ι_z, C.ι_y]
  rw [heq, Subgroup.mem_map] at hf
  obtain ⟨c, hc, rfl⟩ := hf
  rcases RH.pZY_cases c ((RH.mem_ZY c).mp hc) with rfl | rfl | rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr (Or.inl C.ι_z)
  · exact Or.inr (Or.inr (Or.inl C.ι_y))
  · exact Or.inr (Or.inr (Or.inr (by rw [map_mul, C.ι_z, C.ι_y])))

include C in
theorem y_ne_one : F.yF ≠ 1 := by
  rw [← C.ι_y, ← map_one C.ι]; exact fun h => RH.y_ne.1 (C.inj h)

include C in
theorem y_ne_z : F.yF ≠ S.z := by
  rw [← C.ι_y, ← C.ι_z]; exact fun h => RH.y_ne.2 (C.inj h)

include C in
theorem exists_r_action {e f : X} (he : e ∈ Olist (S := S) (F := F))
    (hf : f = F.yF ∨ f = S.z * F.yF) :
    ∃ r ∈ D.R, r * S.t * r⁻¹ = e ∧ r * F.yF * r⁻¹ = f ∧ r * S.z * r⁻¹ = S.z ∧
      r * F.kF * r⁻¹ = F.kF ∧ (r ∈ D.T₂ ↔ (e = S.t ∨ e = S.t * S.z)) := by
  obtain ⟨c, hc, rfl⟩ := C.mem_Olist.mp he
  obtain ⟨d, hd, rfl⟩ : ∃ d ∈ [RH.y, RH.z * RH.y], C.ι d = f := by
    rcases hf with rfl | rfl
    · exact ⟨RH.y, by simp, C.ι_y⟩
    · exact ⟨RH.z * RH.y, by simp, by rw [map_mul, C.ι_z, C.ι_y]⟩
  obtain ⟨r, h1, h2, h3, h4, h5⟩ := RH.r_action c hc d hd
  refine ⟨C.ι r, C.ι_mem_R r, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← C.ι_t, ← map_inv, ← map_mul, ← map_mul, h1]
  · rw [← C.ι_y, ← map_inv, ← map_mul, ← map_mul, h2]
  · rw [← C.ι_z, ← map_inv, ← map_mul, ← map_mul, h3]
  · rw [← C.ι_k, ← map_inv, ← map_mul, ← map_mul, h4]
  · rw [C.ι_mem_T₂, h5, ← C.ι_t, ← C.ι_z, ← map_mul]
    exact ⟨fun h => h.imp (congrArg C.ι) (congrArg C.ι), fun h => h.imp (fun h' => C.inj h')
      (fun h' => C.inj h')⟩

omit [Finite X] in
theorem comm_of_conj {c a : X} (h : c * a * c⁻¹ = a) : a * c = c * a := by
  calc a * c = (c * a * c⁻¹) * c := by rw [h]
    _ = c * a := by group

theorem mem_centralizer_E {c : X} {yi : X} (hz : c * S.z * c⁻¹ = S.z)
    (hy : c * yi * c⁻¹ = yi) (ht : c * S.t * c⁻¹ = S.t) (hk : c * S.k * c⁻¹ = S.k) :
    c ∈ centralizer (S.E yi : Set X) := by
  have hle : S.E yi ≤ centralizer ({c} : Set X) := by
    rw [A7Base.E, closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    rcases hg with rfl | rfl | rfl | rfl
    · exact comm_of_conj hz
    · exact comm_of_conj hy
    · exact comm_of_conj ht
    · exact comm_of_conj hk
  rw [mem_centralizer_iff]
  intro h hh
  exact mem_centralizer_singleton_iff.mp (hle hh)

omit [Finite X] in
theorem eq_one_of_conj_eq_one {n a : X} (h : n * a * n⁻¹ = 1) : a = 1 := by
  calc a = n⁻¹ * (n * a * n⁻¹) * n := by group
    _ = 1 := by rw [h]; group

include C in
theorem exists_r {n : X} (hnE : n ∈ normalizer (F.E₁ : Set X))
    (hnT : n ∈ normalizer (D.T₂ : Set X)) :
    ∃ r ∈ D.R, r⁻¹ * n ∈ centralizer (F.E₁ : Set X) ∧
      (r ∈ D.T₂ ↔ (n * S.t * n⁻¹ = S.t ∨ n * S.t * n⁻¹ = S.t * S.z)) := by
  have htE : S.t ∈ F.E₁ := subset_closure (by simp)
  have heE : n * S.t * n⁻¹ ∈ F.E₁ := (mem_normalizer_iff.mp hnE S.t).mp htE
  have heO : n * S.t * n⁻¹ ∈ Olist (S := S) (F := F) := by
    have := (D.orbit _ heE).mp ⟨n, hnE, rfl⟩
    simp only [Olist, List.mem_cons, List.not_mem_nil, or_false]
    exact this
  have hnz : n * S.z * n⁻¹ = S.z := by
    have hτ : n * D.w * n⁻¹ ∈ D.T₂ := (mem_normalizer_iff.mp hnT D.w).mp (w_mem_T₂ D)
    have h1 : n * S.z * n⁻¹ = (n * S.t * n⁻¹)⁻¹ *
        ((n * D.w * n⁻¹) * (n * S.t * n⁻¹) * (n * D.w * n⁻¹)⁻¹) := by
      calc n * S.z * n⁻¹ = (n * S.t * n⁻¹)⁻¹ * (n * (S.t * S.z) * n⁻¹) := by group
        _ = (n * S.t * n⁻¹)⁻¹ * (n * (D.w * S.t * D.w⁻¹) * n⁻¹) := by rw [D.w_t]
        _ = _ := by group
    obtain ⟨-, hez⟩ := C.O_facts heO
    rcases C.T₂_conj_O hτ heO with h | h
    · rw [h, inv_mul_cancel] at h1
      exact absurd (eq_one_of_conj_eq_one h1) S.z_ne_one
    · rw [h1, h, ← hez, inv_mul_cancel_left]
  have hny : n * F.yF * n⁻¹ = F.yF ∨ n * F.yF * n⁻¹ = S.z * F.yF := by
    rcases C.mem_closure_zy (D.zy_normal n hnE).2 with h | h | h | h
    · exact absurd (eq_one_of_conj_eq_one h) C.y_ne_one
    · exfalso
      apply C.y_ne_z
      have h' : n * F.yF * n⁻¹ = n * S.z * n⁻¹ := by rw [h, hnz]
      simpa using h'
    · exact Or.inl h
    · exact Or.inr h
  have hnk : n * F.kF * n⁻¹ = F.kF := D.k_fixed n hnE
  obtain ⟨r, hrR, hrt, hry, hrz, hrk, hrT⟩ := C.exists_r_action heO hny
  refine ⟨r, hrR, ?_, hrT⟩
  have key : ∀ a : X, r * a * r⁻¹ = n * a * n⁻¹ → (r⁻¹ * n) * a * (r⁻¹ * n)⁻¹ = a := by
    intro a h
    calc (r⁻¹ * n) * a * (r⁻¹ * n)⁻¹ = r⁻¹ * (n * a * n⁻¹) * r := by group
      _ = r⁻¹ * (r * a * r⁻¹) * r := by rw [h]
      _ = a := by group
  rw [A7Base.Frame.E₁]
  refine mem_centralizer_E (key _ (hrz.trans hnz.symm)) (key _ hry) (key _ hrt) ?_
  rw [← C.kF_eq]
  exact key _ (hrk.trans hnk.symm)

include C in
theorem T₂_cases {r : X} (hr : r ∈ D.R) : r ∈ D.T₂ ∨ D.w₂⁻¹ * r ∈ D.T₂ := by
  obtain ⟨c, rfl⟩ := C.mem_R.mp hr
  rw [C.ι_mem_T₂, ← C.ι_w₂, ← map_inv, ← map_mul, C.ι_mem_T₂]
  exact RH.T2_cases c

include C in
theorem sq_of_mem_E₁ {e : X} (he : e ∈ F.E₁) : e * e = 1 :=
  C.sq_of_mem_Fs (i := 0) (C.Fs_zero ▸ he)

include C in
theorem E₁_le_T₂ : F.E₁ ≤ D.T₂ := C.Fs_zero ▸ C.Fs_le_T₂ (i := 0) (by decide)

include C in
theorem acts_of_centralizer {c : X} (hcE : c ∈ centralizer (F.E₁ : Set X))
    (hcT : c ∈ normalizer (D.T₂ : Set X)) :
    ∃ e ∈ F.E₁, ∀ a ∈ D.T₂, c * a * c⁻¹ = e * a * e⁻¹ := by
  have hδ : ∀ a ∈ D.T₂, a⁻¹ * (c * a * c⁻¹) ∈ F.E₁ := by
    intro a ha
    have hmemT : a⁻¹ * (c * a * c⁻¹) ∈ D.T₂ :=
      mul_mem (inv_mem ha) ((mem_normalizer_iff.mp hcT a).mp ha)
    have hmemC : a⁻¹ * (c * a * c⁻¹) ∈ centralizer (F.E₁ : Set X) := by
      rw [mem_centralizer_iff]
      intro f hf
      have haE : a ∈ normalizer (F.E₁ : Set X) := by
        have := ha
        rw [D.T₂_eq] at this
        exact this.2
      have hf' : a * f * a⁻¹ ∈ F.E₁ := (mem_normalizer_iff.mp haE f).mp hf
      have h1 : f * c = c * f := (mem_centralizer_iff.mp hcE) f hf
      have h2 : (a * f * a⁻¹) * c = c * (a * f * a⁻¹) := (mem_centralizer_iff.mp hcE) _ hf'
      have h3 : f * c⁻¹ = c⁻¹ * f := by
        calc f * c⁻¹ = c⁻¹ * (c * f) * c⁻¹ := by group
          _ = c⁻¹ * (f * c) * c⁻¹ := by rw [h1]
          _ = c⁻¹ * f := by group
      calc f * (a⁻¹ * (c * a * c⁻¹)) = a⁻¹ * ((a * f * a⁻¹) * c) * a * c⁻¹ := by group
        _ = a⁻¹ * (c * (a * f * a⁻¹)) * a * c⁻¹ := by rw [h2]
        _ = a⁻¹ * c * a * (f * c⁻¹) := by group
        _ = a⁻¹ * c * a * (c⁻¹ * f) := by rw [h3]
        _ = a⁻¹ * (c * a * c⁻¹) * f := by group
    have h : a⁻¹ * (c * a * c⁻¹) ∈ D.R ⊓ centralizer (F.E₁ : Set X) :=
      Subgroup.mem_inf.mpr ⟨D.T₂_le hmemT, hmemC⟩
    rw [D.R_inf_centralizer] at h
    exact h
  have hc2 : ∀ a ∈ D.T₂, c ^ 2 * a * (c ^ 2)⁻¹ = a := by
    intro a ha
    have hcδ : c * (a⁻¹ * (c * a * c⁻¹)) * c⁻¹ = a⁻¹ * (c * a * c⁻¹) := by
      have := (mem_centralizer_iff.mp hcE) _ (hδ a ha)
      rw [← this]; group
    have hsq := C.sq_of_mem_E₁ (hδ a ha)
    calc c ^ 2 * a * (c ^ 2)⁻¹ = c * (a * (a⁻¹ * (c * a * c⁻¹))) * c⁻¹ := by
          rw [pow_two]; group
      _ = (c * a * c⁻¹) * (c * (a⁻¹ * (c * a * c⁻¹)) * c⁻¹) := by group
      _ = a * ((a⁻¹ * (c * a * c⁻¹)) * (a⁻¹ * (c * a * c⁻¹))) := by rw [hcδ]; group
      _ = a := by rw [hsq, mul_one]
  have hc2' : ∀ j : ℤ, ∀ a ∈ D.T₂, (c ^ 2) ^ j * a * ((c ^ 2) ^ j)⁻¹ = a := by
    have hmem : c ^ 2 ∈ centralizer (D.T₂ : Set X) := by
      rw [mem_centralizer_iff]
      intro a ha
      have := hc2 a ha
      calc a * c ^ 2 = (c ^ 2 * a * (c ^ 2)⁻¹) * c ^ 2 := by rw [this]
        _ = c ^ 2 * a := by group
    intro j a ha
    have := (mem_centralizer_iff.mp (zpow_mem hmem j)) a ha
    rw [← this]; group
  obtain ⟨k, m, hm, hom⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have he2 : (c ^ m) ^ 2 ^ k = 1 := by
    rw [← pow_mul, mul_comm, ← hom, pow_orderOf_eq_one]
  have hp : IsPGroup 2 (zpowers (c ^ m)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one he2)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  have hle : zpowers (c ^ m) ≤ centralizer (F.E₁ : Set X) := by
    rw [zpowers_le]; exact pow_mem hcE m
  have heE : c ^ m ∈ F.E₁ := D.le_E _ hp hle (mem_zpowers _)
  refine ⟨c ^ m, heE, fun a ha => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ, (1 : ℤ) - m = 2 * j := by
    obtain ⟨i, hi⟩ := hm
    exact ⟨-i, by rw [hi]; push_cast; ring⟩
  have hsplit : c = c ^ m * (c ^ 2) ^ j := by
    have h : (m : ℤ) + 2 * j = 1 := by omega
    calc c = c ^ ((m : ℤ) + 2 * j) := by rw [h, zpow_one]
      _ = c ^ m * (c ^ 2) ^ j := by rw [zpow_add, zpow_mul, zpow_natCast, zpow_ofNat]
  have := hc2' j a ha
  calc c * a * c⁻¹ = c ^ m * ((c ^ 2) ^ j * a * ((c ^ 2) ^ j)⁻¹) * (c ^ m)⁻¹ := by
        conv_lhs => rw [hsplit]
        group
    _ = c ^ m * a * (c ^ m)⁻¹ := by rw [this]

theorem mem_M_of_fix {n : X} (hnT : n ∈ normalizer (D.T₂ : Set X))
    (h0 : conjSub n (C.Fs 0) = C.Fs 0) (h1 : conjSub n (C.Fs 1) = C.Fs 1) : n ∈ M D := by
  have hnE : n ∈ normalizer (F.E₁ : Set X) := by
    rw [← C.Fs_zero]; exact conjSub_eq_self_iff.mp h0
  obtain ⟨r, hrR, hrc, -⟩ := C.exists_r hnE hnT
  have hrT : r ∈ normalizer (D.T₂ : Set X) := conjSub_eq_self_iff.mp (conjSub_R D hrR)
  have hcT : r⁻¹ * n ∈ normalizer (D.T₂ : Set X) := mul_mem (inv_mem hrT) hnT
  obtain ⟨e, heE, hce⟩ := C.acts_of_centralizer hrc hcT
  have heT : e ∈ D.T₂ := C.E₁_le_T₂ heE
  have hr1 : conjSub r (C.Fs 1) = C.Fs 1 := by
    have hc1 : conjSub (r⁻¹ * n) (C.Fs 1) = C.Fs 1 := by
      rw [conjSub_eq_of_acts (C.Fs_le_T₂ (i := 1) (by decide)) hce]
      exact C.conjSub_T₂ (by decide) heT
    calc conjSub r (C.Fs 1) = conjSub r (conjSub (r⁻¹ * n) (C.Fs 1)) := by rw [hc1]
      _ = conjSub n (C.Fs 1) := by rw [← conjSub_mul, mul_inv_cancel_left]
      _ = C.Fs 1 := h1
  have hrT₂ : r ∈ D.T₂ := by
    rcases C.T₂_cases hrR with h | h
    · exact h
    · exfalso
      have h4 : conjSub r (C.Fs 1) = C.Fs 4 := by
        calc conjSub r (C.Fs 1) = conjSub D.w₂ (conjSub (D.w₂⁻¹ * r) (C.Fs 1)) := by
              rw [← conjSub_mul, mul_inv_cancel_left]
          _ = conjSub D.w₂ (C.Fs 1) := by rw [C.conjSub_T₂ (by decide) h]
          _ = C.Fs 4 := C.conjSub_w₂ 1
      exact C.Fs_ne (i := 4) (j := 1) (by decide) (h4.symm.trans hr1)
  refine ⟨hnT, r * e, mul_mem hrT₂ heT, fun a ha => ?_⟩
  have := hce a ha
  calc n * a * n⁻¹ = r * ((r⁻¹ * n) * a * (r⁻¹ * n)⁻¹) * r⁻¹ := by group
    _ = r * (e * a * e⁻¹) * r⁻¹ := by rw [this]
    _ = r * e * a * (r * e)⁻¹ := by group

theorem Acts.mem_M {n : X} {π : Fin 8 → Fin 8} (hn : C.Acts n π)
    (hnT : n ∈ normalizer (D.T₂ : Set X)) (h0 : π 0 = 0) (h1 : π 1 = 1) : n ∈ M D :=
  C.mem_M_of_fix hnT (by rw [hn 0 (by decide), h0]) (by rw [hn 1 (by decide), h1])

theorem acts_M {m : X} (hm : m ∈ M D) : C.Acts m id := by
  obtain ⟨-, τ, hτ, hmτ⟩ := hm
  intro i hi
  rw [conjSub_eq_of_acts (C.Fs_le_T₂ hi) hmτ, C.conjSub_T₂ hi hτ, id]

include C in
theorem M_fix_z_k {m : X} (hm : m ∈ M D) : m * S.z * m⁻¹ = S.z ∧ m * F.kF * m⁻¹ = F.kF := by
  obtain ⟨-, τ, hτ, hmτ⟩ := hm
  rw [hmτ _ (z_mem_T₂ D), hmτ _ (k_mem_T₂ D)]
  obtain ⟨h1, h2⟩ := C.comm_z_k (D.T₂_le hτ)
  exact ⟨by rw [h1, mul_inv_cancel_right], by rw [h2, mul_inv_cancel_right]⟩

end Setup

end Sec5H

end CFSG.ComponentClassification.HSFLit
