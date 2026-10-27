module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARem
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL49C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Lemma31Cent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Cnt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Prod

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma isPGroup_of_isElemAbelian {p : ℕ} {A : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian p A) : IsPGroup p A := by
  intro x
  refine ⟨1, ?_⟩
  rw [pow_one]
  exact Subtype.ext (by simpa using hA.2 (x : G) x.2)

private lemma isMulCommutative_map_of_injective {E : Subgroup G}
    (hE : IsMulCommutative ↥E) (f : G →* G) (hf : Function.Injective f) :
    IsMulCommutative ↥(E.map f) := by
  haveI : IsMulCommutative ↥E := hE
  refine IsMulCommutative.of_comm fun x y => Subtype.ext ?_
  obtain ⟨a, ha, hxa⟩ := Subgroup.mem_map.mp x.2
  obtain ⟨b, hb, hxb⟩ := Subgroup.mem_map.mp y.2
  show (x : G) * (y : G) = (y : G) * (x : G)
  rw [← hxa, ← hxb, ← map_mul, ← map_mul]
  exact congrArg f (congrArg (Subtype.val : ↥E → G)
    (mul_comm' (⟨a, ha⟩ : ↥E) (⟨b, hb⟩ : ↥E)))

private lemma isElemAbelian_map_of_injective {p : ℕ} {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) (f : G →* G) (hf : Function.Injective f) :
    CFSG.Open.IsElemAbelian p (E.map f) := by
  refine ⟨isMulCommutative_map_of_injective hE.1 f hf, ?_⟩
  intro x hx
  obtain ⟨a, ha, hxa⟩ := Subgroup.mem_map.mp hx
  rw [← hxa, ← map_pow]
  simpa using congrArg f (hE.2 a ha)

private lemma isElemAbelian_of_le {p : ℕ} {E E₀ : Subgroup G}
    (hE₀ : CFSG.Open.IsElemAbelian p E₀) (hEE₀ : E ≤ E₀) :
    CFSG.Open.IsElemAbelian p E := by
  refine ⟨IsMulCommutative.of_comm fun x y => Subtype.ext ?_,
    fun x hx => hE₀.2 x (hEE₀ hx)⟩
  haveI : IsMulCommutative ↥E₀ := hE₀.1
  exact congrArg (Subtype.val : ↥E₀ → G) (mul_comm' (⟨(x : G), hEE₀ x.2⟩ : ↥E₀)
    (⟨(y : G), hEE₀ y.2⟩ : ↥E₀))

theorem c17_cent_eq (hc : Ctx10 t L S x₁ x₂ lam rho tau) {R : Subgroup G} (hR : IsPGroup 2 R)
    (hSR : S ≤ R) : R ⊓ centralizer ({t} : Set G) = S := by
  have hS_le : S ≤ R ⊓ centralizer ({t} : Set G) := le_inf hSR hc.le_invCent
  have hQp : IsPGroup 2 (R ⊓ centralizer ({t} : Set G) : Subgroup G) := hR.to_le inf_le_left
  exact S4A.eq_of_isPGroup_of_odd_relIndex hS_le inf_le_right hQp hc.relIndex_odd

theorem c17_card_elemAbelian_le (hc : Ctx10 t L S x₁ x₂ lam rho tau) {A : Subgroup G}
    (hAS : A ≤ S) (hA : CFSG.Open.IsElemAbelian 2 A) : Nat.card A ≤ 16 := by
  by_contra hle
  have hlt : 16 < Nat.card A := Nat.lt_of_not_le hle
  have hA2 : IsPGroup 2 A := isPGroup_of_isElemAbelian hA
  have h16 : 2 ^ 4 ≤ Nat.card A := by
    have h : (16 : ℕ) ≤ Nat.card A := le_of_lt hlt
    simpa using h
  obtain ⟨Y', -, hY'card⟩ := Sylow.exists_subgroup_le_card_pow_prime_of_le_card
    (p := 2) (n := 4) Nat.prime_two hA2 (H := (⊤ : Subgroup ↥A))
      (by rw [Subgroup.card_top]; exact h16)
  let Y : Subgroup G := Y'.map A.subtype
  have hYA : Y ≤ A := Subgroup.map_subtype_le Y'
  have hYS : Y ≤ S := hYA.trans hAS
  have hYe : CFSG.Open.IsElemAbelian 2 Y := isElemAbelian_of_le hA hYA
  have hYcard : Nat.card Y = 16 := by
    change Nat.card (Y'.map A.subtype) = 16
    rw [Subgroup.card_subtype, hY'card]
    norm_num
  have hY16 : IsE16In S Y := ⟨hYS, hYe, hYcard⟩
  have hcent : S ⊓ centralizer (Y : Set G) = Y := (hc.l47.1 Y hY16).2.2
  have hAc : A ≤ centralizer (Y : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyA : y ∈ A := hYA hy
    haveI : IsMulCommutative ↥A := hA.1
    exact congrArg Subtype.val (mul_comm' (⟨y, hyA⟩ : ↥A) (⟨a, ha⟩ : ↥A))
  have hAle : A ≤ S ⊓ centralizer (Y : Set G) := le_inf hAS hAc
  have hcard := Subgroup.card_le_of_le hAle
  rw [hcent, hYcard] at hcard
  omega

theorem c17_exists_conj (hc : Ctx10 t L S x₁ x₂ lam rho tau) (g : G) {A : Subgroup G}
    (hA : IsPGroup 2 A) (hAc : A ≤ centralizer ({g * t * g⁻¹} : Set G)) :
    ∃ k : G, ∀ a ∈ A, k * a * k⁻¹ ∈ S := by
  let A' : Subgroup G := A.map (MulAut.conj g⁻¹).toMonoidHom
  have hA'p : IsPGroup 2 A' := by
    change IsPGroup 2 (A.map (MulAut.conj g⁻¹).toMonoidHom)
    exact hA.map (MulAut.conj g⁻¹).toMonoidHom
  have hA'c : A' ≤ centralizer ({t} : Set G) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hqcomm : a * (g * t * g⁻¹) = (g * t * g⁻¹) * a :=
      Subgroup.mem_centralizer_singleton_iff.mp (hAc ha)
    have hconj : (MulAut.conj g⁻¹) (g * t * g⁻¹) = t := by
      rw [MulAut.conj_apply]; group
    have key : (MulAut.conj g⁻¹) a * t = t * (MulAut.conj g⁻¹) a := by
      have h := congrArg (MulAut.conj g⁻¹) hqcomm
      simpa only [map_mul, hconj] using h
    exact key
  obtain ⟨k, -, hk⟩ := S4A.exists_conj_le_of_isPGroup hA'c hA'p hc.le_invCent
    hc.isPGroup hc.relIndex_odd
  refine ⟨k * g⁻¹, fun a ha => ?_⟩
  have ha' : (MulAut.conj g⁻¹) a ∈ A' := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  have hka := hk _ ha'
  have heq : (k * g⁻¹) * a * (k * g⁻¹)⁻¹ = k * (MulAut.conj g⁻¹) a * k⁻¹ := by
    rw [MulAut.conj_apply]; group
  rw [heq]; exact hka

theorem c17_card_elemAbelian_conj_le (hc : Ctx10 t L S x₁ x₂ lam rho tau) (g : G)
    {A : Subgroup G} (hAc : A ≤ centralizer ({g * t * g⁻¹} : Set G))
    (hA : CFSG.Open.IsElemAbelian 2 A) : Nat.card A ≤ 16 := by
  have hA2 : IsPGroup 2 A := isPGroup_of_isElemAbelian hA
  obtain ⟨k, hk⟩ := c17_exists_conj hc g hA2 hAc
  let A'' : Subgroup G := A.map (MulAut.conj k).toMonoidHom
  have hA''S : A'' ≤ S := by
    rintro x ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using hk a ha
  have hA''e : CFSG.Open.IsElemAbelian 2 A'' :=
    isElemAbelian_map_of_injective hA (MulAut.conj k).toMonoidHom (MulAut.conj k).injective
  have hcard : Nat.card A'' = Nat.card A := by
    change Nat.card (A.map (MulAut.conj k).toMonoidHom) = Nat.card A
    exact Subgroup.card_map_of_injective (MulAut.conj k).injective
  calc Nat.card A = Nat.card A'' := hcard.symm
    _ ≤ 16 := c17_card_elemAbelian_le hc hA''S hA''e

theorem c17_card_abelian_ord_eight_le (hc : Ctx10 t L S x₁ x₂ lam rho tau) (g : G)
    {A : Subgroup G} (hAc : A ≤ centralizer ({g * t * g⁻¹} : Set G))
    (hAab : IsMulCommutative A) (hA2 : IsPGroup 2 A) {w : G} (hw : w ∈ A) (hw8 : orderOf w = 8) :
    Nat.card A ≤ 16 := by
  obtain ⟨k, hk⟩ := c17_exists_conj hc g hA2 hAc
  let A'' : Subgroup G := A.map (MulAut.conj k).toMonoidHom
  let w'' : G := (MulAut.conj k) w
  have hA''S : A'' ≤ S := by
    rintro x ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using hk a ha
  have hA''ab : IsMulCommutative ↥A'' :=
    isMulCommutative_map_of_injective hAab (MulAut.conj k).toMonoidHom
      (MulAut.conj k).injective
  have hw'' : w'' ∈ A'' := Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
  have hw''8 : orderOf w'' = 8 := by
    change orderOf ((MulAut.conj k) w) = 8
    rw [MulEquiv.orderOf_eq, hw8]
  have hS_eq : S = zpowers t ⊔ m12Grp x₁ x₂ lam tau := (Ctx4.S_eq_prod hc.toCtx4).1
  have ht_cent : t ∈ centralizer (S : Set G) := by
    have h := Ctx4.center_S hc.toCtx4
    have : t ∈ S ⊓ centralizer (S : Set G) := by
      rw [h]
      exact Subgroup.subset_closure (by simp)
    exact this.2
  have hcent_t : ∀ h ∈ zpowers t, h ∈ centralizer (S : Set G) :=
    fun h hh => Subgroup.zpowers_le.mpr ht_cent hh
  have hcomm_t : ∀ h ∈ zpowers t, ∀ s ∈ S, h * s = s * h :=
    fun h hh s hs => ((Subgroup.mem_centralizer_iff.mp (hcent_t h hh)) s hs).symm
  have hcomm_zz : ∀ a ∈ zpowers t, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.refl t).zpow_zpow i j).eq
  have hnorm : ∀ x ∈ m12Grp x₁ x₂ lam tau, ∀ h ∈ zpowers t, x * h * x⁻¹ ∈ zpowers t := by
    intro x hx h hh
    have hxS : x ∈ S := by
      rw [hS_eq]; exact Subgroup.mem_sup_right hx
    have hxh := hcomm_t h hh x hxS
    have : x * h * x⁻¹ = h := by rw [← hxh]; group
    rw [this]; exact hh
  have hw''S : w'' ∈ S := hA''S hw''
  obtain ⟨w_t, hw_t, m, hmM, hw_eq⟩ :=
    (mem_sup_iff_of_normalizes (H := zpowers t) (K := m12Grp x₁ x₂ lam tau) hnorm).mp
      (by rw [← hS_eq]; exact hw''S)
  have hmS : m ∈ S := by rw [hS_eq]; exact Subgroup.mem_sup_right hmM
  have hcm : Commute w_t m := hcomm_t w_t hw_t m hmS
  have hwt2 : w_t ^ 2 = 1 := by
    have hdvd : orderOf w_t ∣ orderOf t := orderOf_dvd_of_mem_zpowers hw_t
    rw [hc.hyp.ord_t] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hwt4 : w_t ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hwt2, one_pow]
  have hwt8 : w_t ^ 8 = 1 := by
    rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, hwt4, one_pow]
  have hw4 : w'' ^ 4 = m ^ 4 := by
    rw [hw_eq, hcm.mul_pow 4, hwt4, one_mul]
  have hw8' : w'' ^ 8 = m ^ 8 := by
    rw [hw_eq, hcm.mul_pow 8, hwt8, one_mul]
  have hw''pow : w'' ^ 8 = 1 := by
    have h := pow_orderOf_eq_one w''
    rwa [hw''8] at h
  have hm8_1 : m ^ 8 = 1 := by rw [← hw8']; exact hw''pow
  have hm4_ne : m ^ 4 ≠ 1 := by
    intro h
    have hw4_1 : w'' ^ 4 = 1 := by rw [hw4, h]
    have hdvd : orderOf w'' ∣ 4 := orderOf_dvd_of_pow_eq_one hw4_1
    rw [hw''8] at hdvd
    exact (by norm_num : ¬ (8 : ℕ) ∣ 4) hdvd
  have hm8 : orderOf m = 8 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnot : ¬ m ^ 2 ^ 2 = 1 := fun h => hm4_ne (by simpa using h)
    have hfin : m ^ 2 ^ (2 + 1) = 1 := by simpa using hm8_1
    have horder := orderOf_eq_prime_pow (p := 2) (n := 2) hnot hfin
    simpa using horder
  have hScent : S ⊓ centralizer ({w''} : Set G) ≤ zpowers t ⊔ zpowers m := by
    intro s hs
    obtain ⟨hsS, hsc⟩ := hs
    obtain ⟨h_t, hht, m', hm'M, rfl⟩ :=
      (mem_sup_iff_of_normalizes (H := zpowers t) (K := m12Grp x₁ x₂ lam tau) hnorm).mp
        (by rw [← hS_eq]; exact hsS)
    have hm'S : m' ∈ S := by rw [hS_eq]; exact Subgroup.mem_sup_right hm'M
    have hcomm_sw : (h_t * m') * w'' = w'' * (h_t * m') :=
      Subgroup.mem_centralizer_singleton_iff.mp hsc
    have h1 : (h_t * m') * w'' = (h_t * w_t) * (m' * m) := by
      rw [hw_eq]
      calc (h_t * m') * (w_t * m) = h_t * (m' * w_t) * m := by group
        _ = h_t * (w_t * m') * m := by rw [hcomm_t w_t hw_t m' hm'S]
        _ = (h_t * w_t) * (m' * m) := by group
    have h2 : w'' * (h_t * m') = (h_t * w_t) * (m * m') := by
      rw [hw_eq]
      calc (w_t * m) * (h_t * m') = w_t * (m * h_t) * m' := by group
        _ = w_t * (h_t * m) * m' := by rw [← hcomm_t h_t hht m hmS]
        _ = (h_t * w_t) * (m * m') := by
              rw [show w_t * (h_t * m) * m' = (w_t * h_t) * (m * m') by group,
                hcomm_zz w_t hw_t h_t hht]
    have hkey : m' * m = m * m' := by
      have hmain : (h_t * w_t) * (m' * m) = (h_t * w_t) * (m * m') := by
        rw [← h1, hcomm_sw, h2]
      exact mul_left_cancel hmain
    have hm'cent : m' ∈ zpowers m := by
      have hmemb : m' ∈ m12Grp x₁ x₂ lam tau ⊓ centralizer ({m} : Set G) :=
        ⟨hm'M, Subgroup.mem_centralizer_singleton_iff.mpr hkey⟩
      rwa [(Ctx4.m12Rel hc.toCtx4).centralizer_eq_zpowers_of_orderOf_eq_eight hmM hm8] at hmemb
    exact Subgroup.mul_mem_sup hht hm'cent
  have hA''cent : A'' ≤ S ⊓ centralizer ({w''} : Set G) := by
    refine le_inf hA''S (fun s hs => ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    haveI : IsMulCommutative ↥A'' := hA''ab
    exact congrArg Subtype.val (mul_comm' (⟨s, hs⟩ : ↥A'') (⟨w'', hw''⟩ : ↥A''))
  have hA''T : A'' ≤ zpowers t ⊔ zpowers m := hA''cent.trans hScent
  have hTcard : Nat.card (zpowers t ⊔ zpowers m : Subgroup G) ≤ 16 := by
    have hnorm2 : ∀ x ∈ zpowers m, ∀ h ∈ zpowers t, x * h * x⁻¹ ∈ zpowers t := by
      intro x hx h hh
      have hxS : x ∈ S := by
        rw [hS_eq]
        exact Subgroup.mem_sup_right (Subgroup.zpowers_le.mpr hmM hx)
      have hxh := hcomm_t h hh x hxS
      have : x * h * x⁻¹ = h := by rw [← hxh]; group
      rw [this]; exact hh
    have hsurj : Function.Surjective (fun p : ↥(zpowers t) × ↥(zpowers m) =>
        (⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩ :
          ↥(zpowers t ⊔ zpowers m))) := by
      intro x
      obtain ⟨h, hh, k, hk, hx⟩ :=
        (mem_sup_iff_of_normalizes (H := zpowers t) (K := zpowers m) hnorm2).mp x.2
      exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext hx.symm⟩
    calc Nat.card (zpowers t ⊔ zpowers m : Subgroup G)
        ≤ Nat.card (↥(zpowers t) × ↥(zpowers m)) :=
          Nat.card_le_card_of_surjective _ hsurj
      _ = Nat.card (zpowers t) * Nat.card (zpowers m) := Nat.card_prod _ _
      _ = 2 * 8 := by rw [Nat.card_zpowers, Nat.card_zpowers, hc.hyp.ord_t, hm8]
      _ = 16 := by norm_num
  have hcard : Nat.card A'' = Nat.card A := by
    change Nat.card (A.map (MulAut.conj k).toMonoidHom) = Nat.card A
    exact Subgroup.card_map_of_injective (MulAut.conj k).injective
  calc Nat.card A = Nat.card A'' := hcard.symm
    _ ≤ 16 := le_trans (Subgroup.card_le_of_le hA''T) hTcard

theorem c17_tG_not_mem_normal (hc : Ctx10 t L S x₁ x₂ lam rho tau) {R A : Subgroup G}
    (hR : IsPGroup 2 R) (hRcard : 2 ^ 12 ≤ Nat.card R) (hAR : NormalIn A R)
    (hA16 : Nat.card A ≤ 16) (g : G) : g * t * g⁻¹ ∉ A := by
  intro hmem
  have ht1 : t ≠ 1 := by
    intro h
    have h2 := hc.hyp.ord_t
    rw [h, orderOf_one] at h2
    norm_num at h2
  have ha1 : g * t * g⁻¹ ≠ 1 := by
    intro h
    apply ht1
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hb := card_le_mul_card_centralizer (R := R) (A := A) hAR.2 hmem ha1 hAR.1
  have hQp : IsPGroup 2 (R ⊓ centralizer ({g * t * g⁻¹} : Set G) : Subgroup G) :=
    hR.to_le inf_le_left
  have hQbound := S4A.card_le_of_isPGroup_le_centralizer_conj (S := S) (t := t)
    hc.le_invCent hc.isPGroup hc.relIndex_odd (Ctx4.card_S_seven hc.toCtx4) g hQp inf_le_right
  have hA1 : Nat.card A - 1 ≤ 15 := by
    haveI : Nonempty A := ⟨⟨1, A.one_mem⟩⟩
    have hpos : 0 < Nat.card A := Nat.card_pos
    omega
  have hRle : Nat.card R ≤ 15 * 2 ^ 7 := by
    calc Nat.card R
        ≤ (Nat.card A - 1) *
            Nat.card (R ⊓ centralizer ({g * t * g⁻¹} : Set G) : Subgroup G) := hb
      _ ≤ 15 * 2 ^ 7 := Nat.mul_le_mul hA1 hQbound
  have : (2 : ℕ) ^ 12 ≤ 15 * 2 ^ 7 := le_trans hRcard hRle
  norm_num at this

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
