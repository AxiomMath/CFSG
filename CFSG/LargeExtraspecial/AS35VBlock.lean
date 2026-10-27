module

public import CFSG.LargeExtraspecial.AS35VFit
public import CFSG.LargeExtraspecial.AS35EFiveOne
public import CFSG.LargeExtraspecial.AS35EResid

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.RankThree.OrthogonalInvolutions
open Setting (comp12_subset_Dbar12 conj_mem_closure_of_conj_mem mem_normalizer_of_conj_le
  commute_of_not_mem_comp12 mem_comp12_self conj_mem_comp12 mem_normalizer_of_commute
  comp12_trans comp12_symm)

namespace AS35V

variable {G : Type} [Group G] [Finite G] {S : Setting G}

@[expose] def PbarSupply (S : Setting G) : Prop :=
  ∀ σ ∈ S.DbarAsc, ∃ P : Subgroup S.O, PbarFacts S σ P ∧
    ∀ Y : Subgroup S.O, Y ≤ S.Mbar → (∀ y ∈ Y, y * σ = σ * y) →
      (∀ p ∈ P, ∀ y ∈ Y, p * y * p⁻¹ ∈ Y) → CFSG.oddCore Y ⊔ CFSG.layer Y = ⊤ → Nat.card Y ≤ 3

theorem mem_Mbar_of_mem_DbarAsc {σ : S.O} (hσ : σ ∈ S.DbarAsc) : σ ∈ S.Mbar := by
  obtain ⟨t, -, ht, rfl⟩ := hσ
  exact ⟨⟨t, ht⟩, rfl⟩

theorem isTypeA_of_mem_DbarAsc (hS : S.SixHyp) {σ : S.O} (hσ : σ ∈ S.DbarAsc) :
    IsTypeA S.q (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 := by
  obtain ⟨t, htD, ht, rfl⟩ := hσ
  exact (S.fiveOne_two hS.sixFour hS.weak htD ht).1

theorem mem_Dbar12_of_mem_DbarAsc (hS : S.SixHyp) {σ : S.O} (hσ : σ ∈ S.DbarAsc) :
    σ ∈ S.Dbar12 :=
  ⟨mem_Mbar_of_mem_DbarAsc hσ, isTypeA_of_mem_DbarAsc hS hσ⟩

theorem conj_mem_DbarAsc {m σ : S.O} (hm : m ∈ S.Mbar) (hσ : σ ∈ S.DbarAsc) :
    m * σ * m⁻¹ ∈ S.DbarAsc := by
  obtain ⟨m', rfl⟩ := hm
  obtain ⟨t, htD, ht, rfl⟩ := hσ
  have hmt : (m' : G) * t * (m' : G)⁻¹ ∈ S.M :=
    S.M.mul_mem (S.M.mul_mem m'.2 ht) (S.M.inv_mem m'.2)
  refine ⟨_, S.conj_mem_DSet m'.2 htD, hmt, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem DbarAsc_nonempty (hS : S.SixHyp) : S.DbarAsc.Nonempty := by
  obtain ⟨t, ht⟩ := S.DSet_nonempty hS.sixFour hS.hSet_nonempty
  exact ⟨_, t, ht, S.mem_M_of_mem_ESet hS.sixFour ht.1, rfl⟩

theorem one_ne_of_mem_DbarAsc (hS : S.SixHyp) {σ : S.O} (hσ : σ ∈ S.DbarAsc) : σ ≠ 1 :=
  fun e => (isTypeA_of_mem_DbarAsc hS hσ).2.1 (by rw [e]; rfl)

theorem mul_self_of_mem_DbarAsc (hS : S.SixHyp) {σ : S.O} (hσ : σ ∈ S.DbarAsc) : σ * σ = 1 :=
  Subtype.ext (isTypeA_of_mem_DbarAsc hS hσ).2.2.1

theorem comp12_subset_DbarAsc (hS : S.SixHyp) (hRI : RootInvolutionComponentsInput.{0})
    {σ : S.O} (hσ : σ ∈ S.DbarAsc) : S.comp12 σ ⊆ S.DbarAsc := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := hRI S.Qt S.q S.q_nondegenerate S.Mbar S.s12_noNormalTwo_Mbar S.Dbar12
    rfl σ (mem_Dbar12_of_mem_DbarAsc hS hσ) e he
  have hxM : x ∈ S.Mbar := by
    refine (closure_le _).mpr (fun y hy => ?_) hx
    exact (comp12_subset_Dbar12 (mem_Dbar12_of_mem_DbarAsc hS hσ) hy).1
  exact conj_mem_DbarAsc hxM hσ

theorem conj_mem_closure_DbarAsc {m : S.O} (hm : m ∈ S.Mbar) {x : S.O}
    (hx : x ∈ closure S.DbarAsc) : m * x * m⁻¹ ∈ closure S.DbarAsc :=
  conj_mem_closure_of_conj_mem (fun _ hy => conj_mem_DbarAsc hm hy) x hx

theorem closure_DbarAsc_le_Mbar : closure S.DbarAsc ≤ S.Mbar :=
  (closure_le _).mpr fun _ hσ => mem_Mbar_of_mem_DbarAsc hσ

theorem Mbar_le_normalizer_closure_DbarAsc :
    S.Mbar ≤ normalizer (closure S.DbarAsc : Set S.O) := fun _ hm =>
  mem_normalizer_of_conj_le (fun _ hx => conj_mem_closure_DbarAsc hm hx)
    (fun _ hx => conj_mem_closure_DbarAsc (S.Mbar.inv_mem hm) hx)

theorem noNormalTwo_closure_DbarAsc : S12NoNormalTwo (closure S.DbarAsc) :=
  S.s12_noNormalTwo_Mbar.of_normal closure_DbarAsc_le_Mbar Mbar_le_normalizer_closure_DbarAsc

theorem eq_one_of_pow_three_of_mul_self {Γ : Type*} [Group Γ] {x : Γ} (h3 : x ^ 3 = 1)
    (h2 : x * x = 1) : x = 1 := by
  calc x = x ^ 3 * (x * x)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; group

theorem exists_of_selfCentralizing_card_eq_three {K : Subgroup S.O} {F : Subgroup K}
    (hFn : F.Normal) (hcent : centralizer (F : Set K) ≤ F) (hF3 : Nat.card F = 3) {e : S.O}
    (heK : e ∈ K) (he1 : e ≠ 1) (hee : e * e = 1) :
    ∃ y ∈ K, y ≠ 1 ∧ y ^ 3 = 1 ∧ e * y * e⁻¹ = y⁻¹ ∧
      ∀ k ∈ K, k ∈ zpowers y ∨ ∃ w ∈ zpowers y, k = e * w := by
  have hFnt : F ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hF3
    omega
  obtain ⟨y₀, hy₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hFnt
  have hy₀3 : y₀ ^ 3 = 1 := by
    have := pow_card_eq_one' (G := F) (x := y₀)
    rw [hF3] at this
    exact this
  have hFz : zpowers (y₀ : K) = F := by
    refine eq_of_le_of_card_ge (zpowers_le.mpr y₀.2) ?_
    rw [Nat.card_zpowers, hF3]
    have h1 : (y₀ : K) ≠ 1 := fun h => hy₀1 (Subtype.ext h)
    have h3 : (y₀ : K) ^ 3 = 1 := congrArg Subtype.val hy₀3
    rw [orderOf_eq_three_of_pow h3 h1]
  obtain ⟨y, hy⟩ : ∃ y : S.O, y = ((y₀ : K) : S.O) := ⟨_, rfl⟩
  have hyK : y ∈ K := hy ▸ (y₀ : K).2
  have hy1 : y ≠ 1 := fun h => hy₀1 (Subtype.ext (Subtype.ext (hy ▸ h)))
  have hy3 : y ^ 3 = 1 := by
    have h1 : ((y₀ ^ 3 : F) : K) = 1 := by rw [hy₀3]; rfl
    have h2 : (((y₀ ^ 3 : F) : K) : S.O) = 1 := by rw [h1]; rfl
    simpa [hy] using h2
  have hmemz : ∀ w : K, w ∈ zpowers (y₀ : K) → (w : S.O) ∈ zpowers y := by
    intro w hw
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hw
    refine ⟨n, ?_⟩
    rw [hy]
    simp
  have hnorm : ∀ k ∈ K, k * y * k⁻¹ ∈ zpowers y := by
    intro k hk
    have h1 : (⟨k, hk⟩ : K) * (y₀ : K) * (⟨k, hk⟩ : K)⁻¹ ∈ F := hFn.conj_mem _ y₀.2 _
    have h2 := hmemz _ (hFz.symm.le h1)
    have e2 : ((⟨k, hk⟩ * (y₀ : K) * (⟨k, hk⟩ : K)⁻¹ : K) : S.O) = k * y * k⁻¹ := by
      rw [hy]
      simp
    rw [← e2]
    exact h2
  have hcy : ∀ k ∈ K, k * y = y * k → k ∈ zpowers y := by
    intro k hk hky
    have h1 : (⟨k, hk⟩ : K) ∈ centralizer (F : Set K) := by
      rw [mem_centralizer_iff]
      intro w hw
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp (hFz.symm.le hw)
      have hc : Commute (⟨k, hk⟩ : K) (y₀ : K) := Subtype.ext (by simpa [hy] using hky)
      exact (hc.zpow_right n).eq.symm
    exact hmemz _ (hFz.symm.le (hcent h1))
  have hey : e * y * e⁻¹ = y⁻¹ := by
    rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers hy3 (hnorm e heK) with h1 | h1 | h1
    · exfalso
      apply hy1
      calc y = e⁻¹ * (e * y * e⁻¹) * e := by group
        _ = 1 := by rw [h1]; group
    · exfalso
      have he' : e ∈ zpowers y := hcy e heK (by
        calc e * y = (e * y * e⁻¹) * e := by group
          _ = y * e := by rw [h1])
      rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers hy3 he' with h2 | h2 | h2
      · exact he1 h2
      · apply hy1
        have hyy : y * y = 1 := by rw [← h2]; exact hee
        calc y = y ^ 3 * (y * y)⁻¹ := by group
          _ = 1 := by rw [hy3, hyy]; group
      · apply hy1
        have : y⁻¹ * y⁻¹ = 1 := by rw [← h2]; exact hee
        calc y = y ^ 3 * (y⁻¹ * y⁻¹) := by group
          _ = 1 := by rw [hy3, this, one_mul]
    · exact h1
  refine ⟨y, hyK, hy1, hy3, hey, fun k hk => ?_⟩
  rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers hy3 (hnorm k hk) with h1 | h1 | h1
  · exfalso
    apply hy1
    calc y = k⁻¹ * (k * y * k⁻¹) * k := by group
      _ = 1 := by rw [h1]; group
  · exact Or.inl (hcy k hk (by
      calc k * y = (k * y * k⁻¹) * k := by group
        _ = y * k := by rw [h1]))
  · right
    have hek : e * k ∈ zpowers y := hcy (e * k) (K.mul_mem heK hk) (by
      have : (e * k) * y * (e * k)⁻¹ = y := by
        calc (e * k) * y * (e * k)⁻¹ = e * (k * y * k⁻¹) * e⁻¹ := by group
          _ = (e * y * e⁻¹)⁻¹ := by rw [h1]; group
          _ = y := by rw [hey, inv_inv]
      calc e * k * y = ((e * k) * y * (e * k)⁻¹) * (e * k) := by group
        _ = y * (e * k) := by rw [this])
    refine ⟨e * k, hek, ?_⟩
    calc k = (e * e) * k := by rw [hee, one_mul]
      _ = e * (e * k) := by group

theorem mem_comp12_of_mem_DbarAsc (hS : S.SixHyp) (hRI : RootInvolutionComponentsInput.{0})
    (hsup : PbarSupply S) {σ e : S.O} (hσ : σ ∈ S.DbarAsc) (he : e ∈ S.DbarAsc) :
    e ∈ S.comp12 σ := by
  by_contra hne
  obtain ⟨P, hP, h58⟩ := hsup σ hσ
  obtain ⟨Pe, hPe, -⟩ := hsup e he
  have hσ12 := mem_Dbar12_of_mem_DbarAsc hS hσ
  obtain ⟨F, hF⟩ : ∃ F : Set S.O, F = {f | f ∈ S.DbarAsc ∧ f ∉ S.comp12 σ} := ⟨_, rfl⟩
  have hmemF : ∀ {f}, f ∈ F ↔ f ∈ S.DbarAsc ∧ f ∉ S.comp12 σ := by
    intro f
    rw [hF]
    rfl
  have heF : e ∈ F := hmemF.mpr ⟨he, hne⟩
  have hFD : F ⊆ S.DbarAsc := fun f hf => (hmemF.mp hf).1
  have hFσ : ∀ f ∈ F, f * σ = σ * f := fun f hf =>
    (commute_of_not_mem_comp12 (mem_comp12_self σ) hσ12
      (mem_Dbar12_of_mem_DbarAsc hS (hmemF.mp hf).1) (hmemF.mp hf).2).symm
  obtain ⟨K, hK⟩ : ∃ K : Subgroup S.O, K = closure F := ⟨_, rfl⟩
  have hKM : K ≤ S.Mbar := hK ▸ (closure_le _).mpr fun f hf => mem_Mbar_of_mem_DbarAsc (hFD hf)
  have hKσ : ∀ y ∈ K, y * σ = σ * y := by
    have : K ≤ centralizer ({σ} : Set S.O) := hK ▸ (closure_le _).mpr fun f hf =>
      mem_centralizer_singleton_iff.mpr (hFσ f hf)
    exact fun y hy => mem_centralizer_singleton_iff.mp (this hy)
  have hconjF : ∀ m ∈ S.Mbar, m * σ = σ * m → ∀ f ∈ F, m * f * m⁻¹ ∈ F := by
    intro m hm hmσ f hf
    refine hmemF.mpr ⟨conj_mem_DbarAsc hm (hFD hf), fun hc => (hmemF.mp hf).2 ?_⟩
    have h1 := conj_mem_comp12 (S.Mbar.inv_mem hm) hc
    have e1 : m⁻¹ * σ * m⁻¹⁻¹ = σ := by
      calc m⁻¹ * σ * m⁻¹⁻¹ = m⁻¹ * (σ * m) := by group
        _ = σ := by rw [← hmσ]; group
    have e2 : m⁻¹ * (m * f * m⁻¹) * m⁻¹⁻¹ = f := by group
    rwa [e1, e2] at h1
  have hPK : ∀ p ∈ P, ∀ y ∈ K, p * y * p⁻¹ ∈ K := by
    intro p hp y hy
    rw [hK] at hy ⊢
    exact conj_mem_closure_of_conj_mem (hconjF p (hP.le_Mbar hp) (hP.commute hp)) y hy
  have hN2 : S12NoNormalTwo K := by
    refine noNormalTwo_closure_DbarAsc.of_normal (hK ▸ closure_mono hFD) ?_
    rw [closure_le]
    intro d hd
    by_cases hdF : d ∈ F
    · exact le_normalizer (hK ▸ subset_closure hdF)
    · have hd' : d ∈ S.comp12 σ := by
        by_contra hd'
        exact hdF (hmemF.mpr ⟨hd, hd'⟩)
      refine mem_normalizer_of_commute fun y hy => ?_
      have : K ≤ centralizer ({d} : Set S.O) := hK ▸ (closure_le _).mpr fun f hf =>
        mem_centralizer_singleton_iff.mpr (commute_of_not_mem_comp12 hd' hσ12
          (mem_Dbar12_of_mem_DbarAsc hS (hmemF.mp hf).1) (hmemF.mp hf).2).symm
      exact (mem_centralizer_singleton_iff.mp (this hy)).symm
  obtain ⟨-, hodd, hF3, hFs⟩ := fitting_of_fiveEight h58 hKM hKσ hPK hN2
  have hcent : centralizer (CFSG.fittingSubgroup K : Set K) ≤ CFSG.fittingSubgroup K := by
    have := CFSG.centralizer_generalizedFitting_le K
    rwa [hFs] at this
  have heK : e ∈ K := hK ▸ subset_closure heF
  have he1 := one_ne_of_mem_DbarAsc hS he
  have hee := mul_self_of_mem_DbarAsc hS he
  have hF3' : Nat.card (CFSG.fittingSubgroup K) = 3 := by
    have h1 : Nat.card (CFSG.fittingSubgroup K) ≠ 1 := by
      intro h1
      have hb : CFSG.fittingSubgroup K = ⊥ := Subgroup.card_eq_one.mp h1
      have : (⟨e, heK⟩ : K) ∈ CFSG.fittingSubgroup K := hcent (by
        rw [mem_centralizer_iff]
        intro w hw
        rw [hb] at hw
        rw [mem_bot.mp hw]
        group)
      rw [hb, mem_bot] at this
      exact he1 (congrArg Subtype.val this)
    rcases hodd with ⟨k, hk⟩
    omega
  obtain ⟨y, hyK, hy1, hy3, hey, hKy⟩ := exists_of_selfCentralizing_card_eq_three
    CFSG.fittingSubgroup_normal hcent hF3' heK he1 hee
  have hnotinv : ∀ x ∈ zpowers y, x * x = 1 → x = 1 := by
    intro x hx hxx
    have hx3 : x ^ 3 = 1 := by
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
    calc x = x ^ 3 * (x * x)⁻¹ := by group
      _ = 1 := by rw [hx3, hxx]; group
  have hew : ∀ w ∈ zpowers y, e * w * e⁻¹ = w⁻¹ := by
    intro w hw
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hw
    rw [← conj_zpow, hey, inv_zpow]
  have hinvol : ∀ w ∈ zpowers y, (e * w) * (e * w) = 1 := by
    intro w hw
    calc e * w * (e * w) = (e * w * e⁻¹) * (e * e) * w := by group
      _ = 1 := by rw [hew w hw, hee]; group
  have hFe : F = S.comp12 e := by
    ext f
    constructor
    · intro hf
      have hfK : f ∈ K := hK ▸ subset_closure hf
      rcases hKy f hfK with hfy | ⟨w, hw, rfl⟩
      · exact absurd (hnotinv f hfy (mul_self_of_mem_DbarAsc hS (hFD hf)))
          (one_ne_of_mem_DbarAsc hS (hFD hf))
      · by_cases hw1 : w = 1
        · rw [hw1, mul_one]
          exact mem_comp12_self e
        · refine Relation.ReflTransGen.single ⟨mem_Dbar12_of_mem_DbarAsc hS he,
            mem_Dbar12_of_mem_DbarAsc hS (hFD hf), fun hc => hw1 (hnotinv w hw ?_)⟩
          have e1 : e * (e * w) = w := by rw [← mul_assoc, hee, one_mul]
          have e2 : e * w * e = w⁻¹ := by
            rw [← hew w hw, inv_eq_of_mul_eq_one_right hee]
          have e3 : w = w⁻¹ := by
            calc w = e * (e * w) := e1.symm
              _ = e * w * e := hc
              _ = w⁻¹ := e2
          calc w * w = w * w⁻¹ := by rw [← e3]
            _ = 1 := mul_inv_cancel w
    · intro hf
      refine hmemF.mpr ⟨comp12_subset_DbarAsc hS hRI he hf, fun hc => hne ?_⟩
      exact comp12_trans hc (comp12_symm hf)
  have hPeK : ∀ p ∈ Pe, ∀ k ∈ K, p * k * p⁻¹ ∈ K := by
    intro p hp k hk
    rw [hK] at hk ⊢
    refine conj_mem_closure_of_conj_mem (fun f hf => ?_) k hk
    rw [hFe] at hf ⊢
    have h1 := conj_mem_comp12 (hPe.le_Mbar hp) hf
    rwa [show p * e * p⁻¹ = e by rw [hPe.commute hp]; group] at h1
  refine hPe.false_of_inverts hy3 hy1 (fun p hp => ?_) hey
  rcases hKy _ (hPeK p hp y hyK) with h | ⟨w, hw, hpw⟩
  · exact h
  · exfalso
    have h2 := hinvol w hw
    rw [← hpw] at h2
    have h3 : (p * y * p⁻¹) ^ 3 = 1 := by rw [conj_pow, hy3]; group
    have h4 : p * y * p⁻¹ = 1 := eq_one_of_pow_three_of_mul_self h3 h2
    apply hy1
    calc y = p⁻¹ * (p * y * p⁻¹) * p := by group
      _ = 1 := by rw [h4]; group

end AS35V

end CFSG.LargeExtraspecial
