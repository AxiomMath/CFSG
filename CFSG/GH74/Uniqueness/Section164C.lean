module

public import CFSG.GH74.Uniqueness.Section164B
public import CFSG.GH74.Uniqueness.Section164Q
public import CFSG.GH74.Uniqueness.Section128Index

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec164

theorem u_not_mem_B0 (c : Conf16 Z M) {n i e : ℕ} (hB : BenderSub Z M c.B0 n i e) :
    c.u ∉ c.B0 := by
  intro hu
  have hcen : (⟨c.u, hu⟩ : ↥c.B0) ∈ center ↥c.B0 := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (B0_le_B c g.2))
  have hdvd := orderOf_dvd_natCard (⟨⟨c.u, hu⟩, hcen⟩ : center ↥c.B0)
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, c.hu2] at hdvd
  exact (Nat.not_even_iff_odd.mpr (odd_card_center_B0 c hB)) (even_iff_two_dvd.mpr hdvd)

omit [Finite X] in
theorem mem_normalizer_zHull_of_mem_normalizer (hZ : IsInvariantInvolutionSet Z) {H : Subgroup X}
    {g : X} (hg : g ∈ normalizer (H : Set X)) : g ∈ normalizer (zHull Z H : Set X) := by
  have key : ∀ k : X, k ∈ normalizer (H : Set X) → ∀ x ∈ zHull Z H, k * x * k⁻¹ ∈ zHull Z H := by
    intro k hk x hx
    have hle : zHull Z H ≤ (zHull Z H).comap (MulAut.conj k).toMonoidHom := by
      refine (closure_le _).mpr ?_
      rintro y ⟨hyZ, hyH⟩
      rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine subset_closure ⟨?_, (mem_normalizer_iff.mp hk y).mp hyH⟩
      have := hZ.2 y hyZ k⁻¹
      rwa [inv_inv] at this
    have := hle hx
    rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have := key g⁻¹ (inv_mem hg) _ hx
    simpa [mul_assoc] using this

omit [Finite X] in
theorem mem_normalizer_sup_zpowers {Q : Subgroup X} {u g : X} (hgQ : g ∈ normalizer (Q : Set X))
    (hu1 : g * u * g⁻¹ ∈ Q ⊔ zpowers u) (hu2 : g⁻¹ * u * g ∈ Q ⊔ zpowers u) :
    g ∈ normalizer ((Q ⊔ zpowers u : Subgroup X) : Set X) := by
  have key : ∀ k : X, k ∈ normalizer (Q : Set X) → k * u * k⁻¹ ∈ Q ⊔ zpowers u →
      Q ⊔ zpowers u ≤ (Q ⊔ zpowers u).comap (MulAut.conj k).toMonoidHom := by
    intro k hk hku
    refine sup_le (fun x hx => ?_) (zpowers_le.mpr ?_)
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mem_sup_left ((mem_normalizer_iff.mp hk x).mp hx)
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hku
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have := key g hgQ hu1 hx
    rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  · intro hx
    have := key g⁻¹ (inv_mem hgQ) (by simpa using hu2) hx
    rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    simpa [mul_assoc] using this

theorem card_centralizer_eq_of_isConj {a b : X} (h : IsConj a b) :
    Nat.card (centralizer ({b} : Set X)) = Nat.card (centralizer ({a} : Set X)) := by
  have ha := card_conjClass_mul_card_centralizer a
  have hb := card_conjClass_mul_card_centralizer b
  have heq : Nat.card {y : X // IsConj y a} = Nat.card {y : X // IsConj y b} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => ⟨fun hy => hy.trans h,
      fun hy => hy.trans h.symm⟩)
  have hpos : 0 < Nat.card {y : X // IsConj y b} := Nat.card_pos_iff.mpr
    ⟨⟨⟨b, IsConj.refl b⟩⟩, inferInstance⟩
  rw [heq] at ha
  exact Nat.eq_of_mul_eq_mul_left hpos (hb.trans ha.symm)

theorem exists_burnside (h163 : Lemma163Stmt Z M) (c : Conf16 Z M)
    (hconj : IsConj c.u (c.u * c.z)) :
    ∃ g ∈ normalizer (c.T1 : Set X), g * c.u * g⁻¹ = c.u * c.z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT1B : ABGLocalTools.IsSylowOf 2 c.T1 c.B := (h163 c).2.2.1
  obtain ⟨g₀, hg₀⟩ := isConj_iff.mp hconj
  have hcard : Nat.card (centralizer ({c.u * c.z} : Set X)) = Nat.card c.B :=
    card_centralizer_eq_of_isConj hconj
  have hT1uz : c.T1 ≤ centralizer ({c.u * c.z} : Set X) := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    have h1 : y * c.u = c.u * y := mem_centralizer_singleton_iff.mp (T1_le_B c hy)
    have h2 : y * c.z = c.z * y := c.hz_T1.2 y hy
    calc y * (c.u * c.z) = (y * c.u) * c.z := by group
      _ = c.u * (y * c.z) := by rw [h1]; group
      _ = c.u * (c.z * y) := by rw [h2]
      _ = c.u * c.z * y := by group
  have hT1card := hT1B.card_eq
  have hS1 : ABGLocalTools.IsSylowOf 2 c.T1 (centralizer ({c.u * c.z} : Set X)) :=
    ABGLocalTools.isSylowOf_of_card hT1uz (by rw [hcard]; exact hT1card)
  set T' := conjugate c.T1 g₀⁻¹ with hT'
  have hmemT' : ∀ x, x ∈ T' ↔ g₀⁻¹ * x * g₀ ∈ c.T1 := by
    intro x
    rw [hT', mem_conjugate_iff, inv_inv]
  have hT'uz : T' ≤ centralizer ({c.u * c.z} : Set X) := by
    intro x hx
    rw [hmemT'] at hx
    have h1 := mem_centralizer_singleton_iff.mp (T1_le_B c hx)
    rw [mem_centralizer_singleton_iff, ← hg₀]
    calc x * (g₀ * c.u * g₀⁻¹) = g₀ * ((g₀⁻¹ * x * g₀) * c.u) * g₀⁻¹ := by group
      _ = g₀ * (c.u * (g₀⁻¹ * x * g₀)) * g₀⁻¹ := by rw [h1]
      _ = g₀ * c.u * g₀⁻¹ * x := by group
  have hT'card : Nat.card T' = Nat.card c.T1 := by
    rw [hT', conjugate]
    exact card_map_of_injective (MulAut.conj g₀⁻¹⁻¹).injective
  have hS2 : ABGLocalTools.IsSylowOf 2 T' (centralizer ({c.u * c.z} : Set X)) :=
    ABGLocalTools.isSylowOf_of_card hT'uz (by rw [hT'card, hcard]; exact hT1card)
  obtain ⟨k, hk, hkT⟩ := ABGLocalTools.IsSylowOf.exists_mem_conj hS2 hS1
  refine ⟨k * g₀, ?_, ?_⟩
  · have hinv : (k * g₀)⁻¹ ∈ normalizer (c.T1 : Set X) := by
      rw [mem_normalizer_iff]
      intro x
      rw [hkT, hmemT']
      have e : (k * g₀)⁻¹ * x * (k * g₀)⁻¹⁻¹ = g₀⁻¹ * (k⁻¹ * x * k) * g₀ := by group
      rw [e]
    simpa using inv_mem hinv
  · have hkc : k * (c.u * c.z) = (c.u * c.z) * k := (mem_centralizer_singleton_iff.mp hk)
    calc k * g₀ * c.u * (k * g₀)⁻¹ = k * (g₀ * c.u * g₀⁻¹) * k⁻¹ := by group
      _ = k * (c.u * c.z) * k⁻¹ := by rw [hg₀]
      _ = c.u * c.z := by rw [hkc]; group

theorem Q_le_B0 (c : Conf16 Z M) : c.Q ≤ c.B0 :=
  ((closure_le _).mpr fun _ hx => hx.1).trans (c.hP.le.trans inf_le_left)

theorem Q_le_M (c : Conf16 Z M) : c.Q ≤ M :=
  ((closure_le _).mpr fun _ hx => hx.1).trans (c.hP.le.trans inf_le_right)

theorem Q_le_T1 (c : Conf16 Z M) : c.Q ≤ c.T1 :=
  ((closure_le _).mpr fun _ hx => hx.1).trans c.hPT1

theorem mem_sup_cases (c : Conf16 Z M) {y : X} (hy : y ∈ c.Q ⊔ zpowers c.u) :
    ∃ x ∈ c.Q, y = x ∨ y = x * c.u := by
  have hle : zpowers c.u ≤ normalizer (c.Q : Set X) := by
    refine zpowers_le.mpr (centralizer_le_normalizer _ ?_)
    rw [mem_centralizer_iff]
    intro h hh
    exact (mem_centralizer_singleton_iff.mp (B0_le_B c (Q_le_B0 c hh)))
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left c.Q (zpowers c.u) hle
  have hy' : y ∈ ((c.Q ⊔ zpowers c.u : Subgroup X) : Set X) := hy
  rw [hset] at hy'
  obtain ⟨x, hx, w, hw, hxw⟩ := Set.mem_mul.mp hy'
  refine ⟨x, hx, ?_⟩
  rcases Bender.eq_one_or_eq_of_mem_zpowers c.u_mul_self hw with h | h
  · left
    rw [← hxw, h, mul_one]
  · right
    rw [← hxw, h]

theorem mem_Q_of_mem_Z (c : Conf16 Z M) {n i e : ℕ} (hB : BenderSub Z M c.B0 n i e) {y : X}
    (hy : y ∈ c.Q ⊔ zpowers c.u) (hyZ : y ∈ Z) : y ∈ c.Q := by
  obtain ⟨x, hx, rfl | rfl⟩ := mem_sup_cases c hy
  · exact hx
  · exfalso
    have hxu : x * c.u = c.u * x := mem_centralizer_singleton_iff.mp (B0_le_B c (Q_le_B0 c hx))
    have hyB : x * c.u ∈ c.B := by
      rw [mem_centralizer_singleton_iff]
      calc x * c.u * c.u = c.u * x * c.u := by rw [hxu]
        _ = c.u * (x * c.u) := by group
    have hyB0 : x * c.u ∈ c.B0 := subset_closure ⟨hyZ, hyB⟩
    apply u_not_mem_B0 c hB
    have e : c.u = x⁻¹ * (x * c.u) := by group
    rw [e]
    exact mul_mem (inv_mem (Q_le_B0 c hx)) hyB0

theorem normalizer_Qu_le
    (S : ZDSetup X Z M) (h162 : Lemma162Stmt Z M) (c : Conf16 Z M)
    {n i e : ℕ} (hB : BenderSub Z M c.B0 n i e) :
    normalizer ((c.Q ⊔ zpowers c.u : Subgroup X) : Set X) ≤ normalizer (c.Q : Set X) := by
  have hQZ := (Q_eq_zHull S h162 c hB).2.2
  have key : ∀ g ∈ normalizer ((c.Q ⊔ zpowers c.u : Subgroup X) : Set X), ∀ x ∈ c.Q,
      g * x * g⁻¹ ∈ c.Q := by
    intro g hg x hx
    by_cases hx1 : x = 1
    · subst hx1
      simp only [mul_one, mul_inv_cancel]
      exact one_mem _
    · have hxZ := (hQZ x hx hx1).1
      have h1 : g * x * g⁻¹ ∈ c.Q ⊔ zpowers c.u := (mem_normalizer_iff.mp hg x).mp (mem_sup_left hx)
      have h2 : g * x * g⁻¹ ∈ Z := by
        have := S.invariant.2 x hxZ g⁻¹
        rwa [inv_inv] at this
      exact mem_Q_of_mem_Z c hB h1 h2
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have := key g⁻¹ (inv_mem hg) _ hx
    simpa [mul_assoc] using this

theorem z_mem_Q
    (S : ZDSetup X Z M) (h162 : Lemma162Stmt Z M) (c : Conf16 Z M) {n i e : ℕ}
    (hB : BenderSub Z M c.B0 n i e) : c.z ∈ c.Q := by
  rw [(Q_eq_zHull S h162 c hB).1]
  exact subset_closure ⟨c.hz, c.z_mem_BM⟩

theorem normalizer_Qu_le_M
    (S : ZDSetup X Z M) (h162 : Lemma162Stmt Z M) (c : Conf16 Z M)
    {n i e : ℕ} (hB : BenderSub Z M c.B0 n i e) :
    normalizer ((c.Q ⊔ zpowers c.u : Subgroup X) : Set X) ≤ M :=
  (normalizer_Qu_le S h162 c hB).trans
    (S.prodDisc.normalizer_le (Q_le_M c) c.hz (z_mem_Q S h162 c hB))

theorem Q_eq_zHull_T1
    (S : ZDSetup X Z M) (h162 : Lemma162Stmt Z M) (c : Conf16 Z M)
    {n i e : ℕ} (hB : BenderSub Z M c.B0 n i e) : c.Q = zHull Z c.T1 := by
  have hQ := Q_eq_zHull S h162 c hB
  apply le_antisymm
  · rw [hQ.1]
    refine closure_mono fun y hy => ⟨hy.1, Q_le_T1 c ?_⟩
    rw [hQ.1]
    exact subset_closure hy
  · rw [hQ.1]
    exact closure_mono fun y hy => ⟨hy.1, c.hT1.le hy.2⟩

theorem mem_normalizer_Qu_of_normalizer_T1
    (S : ZDSetup X Z M) (h162 : Lemma162Stmt Z M)
    (c : Conf16 Z M) {n i e : ℕ} (hB : BenderSub Z M c.B0 n i e) {g : X}
    (hg : g ∈ normalizer (c.T1 : Set X)) (hgu : g * c.u * g⁻¹ = c.u * c.z) :
    g ∈ normalizer ((c.Q ⊔ zpowers c.u : Subgroup X) : Set X) := by
  have hgQ : g ∈ normalizer (c.Q : Set X) := by
    rw [Q_eq_zHull_T1 S h162 c hB]
    exact mem_normalizer_zHull_of_mem_normalizer S.invariant hg
  have hzQ := z_mem_Q S h162 c hB
  refine mem_normalizer_sup_zpowers hgQ ?_ ?_
  · rw [hgu]
    exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left hzQ)
  · have hzQ' : g⁻¹ * c.z * g ∈ c.Q := by
      have := (mem_normalizer_iff.mp (inv_mem hgQ) c.z).mp hzQ
      simpa using this
    have e : g⁻¹ * c.u * g = c.u * (g⁻¹ * c.z * g)⁻¹ := by
      have h1 : c.u = g⁻¹ * (c.u * c.z) * g := by rw [← hgu]; group
      calc g⁻¹ * c.u * g = g⁻¹ * c.u * g * (g⁻¹ * c.z * g) * (g⁻¹ * c.z * g)⁻¹ := by group
        _ = (g⁻¹ * (c.u * c.z) * g) * (g⁻¹ * c.z * g)⁻¹ := by group
        _ = c.u * (g⁻¹ * c.z * g)⁻¹ := by rw [← h1]
    rw [e]
    exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (inv_mem hzQ'))

theorem mem_normalizer_Qu_of_commute {c : Conf16 Z M} {g : X} (hgQ : g ∈ normalizer (c.Q : Set X))
    (hgu : g * c.u = c.u * g) : g ∈ normalizer ((c.Q ⊔ zpowers c.u : Subgroup X) : Set X) := by
  refine mem_normalizer_sup_zpowers hgQ ?_ ?_
  · rw [hgu, mul_inv_cancel_right]
    exact mem_sup_right (mem_zpowers _)
  · have : g⁻¹ * c.u * g = c.u := by
      calc g⁻¹ * c.u * g = g⁻¹ * (c.u * g) := by group
        _ = g⁻¹ * (g * c.u) := by rw [hgu]
        _ = c.u := by group
    rw [this]
    exact mem_sup_right (mem_zpowers _)

theorem orbit_u_eq
    (S : ZDSetup X Z M) (h162 : Lemma162Stmt Z M) (h163 : Lemma163Stmt Z M)
    (c : Conf16 Z M) {n i e : ℕ} (hB : BenderSub Z M c.B0 n i e)
    (hconj : IsConj c.u (c.u * c.z)) {y : X} :
    (∃ g ∈ normalizer ((c.Q ⊔ zpowers c.u : Subgroup X) : Set X), g * c.u * g⁻¹ = y) ↔
      ∃ x ∈ c.Q, y = x * c.u := by
  have hNQ := normalizer_Qu_le S h162 c hB
  have huQ : c.u ∉ c.Q := fun h => u_not_mem_B0 c hB (Q_le_B0 c h)
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hmem : g * c.u * g⁻¹ ∈ c.Q ⊔ zpowers c.u :=
      (mem_normalizer_iff.mp hg c.u).mp (mem_sup_right (mem_zpowers _))
    obtain ⟨x, hx, h | h⟩ := mem_sup_cases c hmem
    · exfalso
      apply huQ
      have hmQ : g * c.u * g⁻¹ ∈ c.Q := by rw [h]; exact hx
      have := (mem_normalizer_iff.mp (inv_mem (hNQ hg)) (g * c.u * g⁻¹)).mp hmQ
      simpa [mul_assoc] using this
    · exact ⟨x, hx, h⟩
  · rintro ⟨x, hx, rfl⟩
    by_cases hx1 : x = 1
    · refine ⟨1, one_mem _, ?_⟩
      rw [hx1]
      group
    · have hxΓ := (Q_eq_zHull S h162 c hB).2.2 x hx hx1
      obtain ⟨d, hd, hdx⟩ := exists_conj_gamma S h162 c hB hxΓ
      obtain ⟨g, hg, hgu⟩ := exists_burnside h163 c hconj
      have hgN := mem_normalizer_Qu_of_normalizer_T1 S h162 c hB hg hgu
      have hdu : d * c.u = c.u * d := (mem_centralizer_singleton_iff.mp (mem_inf.mp hd).1)
      have hdQ : d ∈ normalizer (c.Q : Set X) := by
        rw [(Q_eq_zHull S h162 c hB).1]
        exact le_normalizer_zHull S.invariant _ hd
      have hdN := mem_normalizer_Qu_of_commute hdQ hdu
      refine ⟨d⁻¹ * g, mul_mem (inv_mem hdN) hgN, ?_⟩
      have hxu : x * c.u = c.u * x :=
        mem_centralizer_singleton_iff.mp (B0_le_B c (Q_le_B0 c hx))
      have hdu' : d⁻¹ * c.u = c.u * d⁻¹ := by
        calc d⁻¹ * c.u = d⁻¹ * (c.u * d) * d⁻¹ := by group
          _ = d⁻¹ * (d * c.u) * d⁻¹ := by rw [hdu]
          _ = c.u * d⁻¹ := by group
      calc d⁻¹ * g * c.u * (d⁻¹ * g)⁻¹ = d⁻¹ * (g * c.u * g⁻¹) * d := by group
        _ = d⁻¹ * (c.u * c.z) * d := by rw [hgu]
        _ = (d⁻¹ * c.u) * c.z * d := by group
        _ = c.u * (d⁻¹ * c.z * d) := by rw [hdu']; group
        _ = c.u * x := by rw [hdx]
        _ = x * c.u := hxu.symm

theorem dvd_card_normalizer_Qu
    (S : ZDSetup X Z M) (h162 : Lemma162Stmt Z M)
    (h163 : Lemma163Stmt Z M) (c : Conf16 Z M) {n i e : ℕ} (hB : BenderSub Z M c.B0 n i e)
    (hconj : IsConj c.u (c.u * c.z)) :
    2 ^ n * Nat.card c.T1 ∣ Nat.card (normalizer ((c.Q ⊔ zpowers c.u : Subgroup X) : Set X)) := by
  set N := normalizer ((c.Q ⊔ zpowers c.u : Subgroup X) : Set X) with hN
  have hQN : c.Q ⊔ zpowers c.u ≤ N := le_normalizer
  have huN : c.u ∈ N := hQN (mem_sup_right (mem_zpowers _))
  have hcl := card_conjClass_mul_card_centralizer (⟨c.u, huN⟩ : ↥N)
  have hclass : Nat.card {y : ↥N // IsConj y ⟨c.u, huN⟩} = Nat.card ↥c.Q := by
    refine Nat.card_congr
      { toFun := fun y => ⟨(y : X) * c.u, ?_⟩
        invFun := fun x => ⟨⟨(x : X) * c.u, hQN (mul_mem (mem_sup_left x.2)
          (mem_sup_right (mem_zpowers _)))⟩, ?_⟩
        left_inv := fun y => by
          apply Subtype.ext
          apply Subtype.ext
          change (y : X) * c.u * c.u = y
          rw [mul_assoc, c.u_mul_self, mul_one]
        right_inv := fun x => by
          apply Subtype.ext
          change (x : X) * c.u * c.u = x
          rw [mul_assoc, c.u_mul_self, mul_one] }
    · obtain ⟨⟨y, hyN⟩, hy⟩ := y
      obtain ⟨⟨g, hgN⟩, hg⟩ := isConj_iff.mp hy.symm
      have hg' : g * c.u * g⁻¹ = y := congrArg Subtype.val hg
      obtain ⟨x, hx, rfl⟩ := (orbit_u_eq S h162 h163 c hB hconj).mp ⟨g, hgN, hg'⟩
      change x * c.u * c.u ∈ c.Q
      rw [mul_assoc, c.u_mul_self, mul_one]
      exact hx
    · obtain ⟨g, hgN, hg⟩ := (orbit_u_eq S h162 h163 c hB hconj).mpr ⟨x, x.2, rfl⟩
      refine (isConj_iff.mpr ⟨⟨g, hgN⟩, Subtype.ext hg⟩).symm
  rw [hclass, (Q_eq_zHull S h162 c hB).2.1] at hcl
  rw [← hcl]
  apply mul_dvd_mul_left
  have hT1N : c.T1 ≤ N := by
    intro y hy
    have hyQ : y ∈ normalizer (c.Q : Set X) := by
      rw [Q_eq_zHull_T1 S h162 c hB]
      exact le_normalizer_zHull S.invariant _ hy
    exact mem_normalizer_Qu_of_commute hyQ (mem_centralizer_singleton_iff.mp (T1_le_B c hy))
  have hle : c.T1.subgroupOf N ≤ centralizer ({⟨c.u, huN⟩} : Set ↥N) := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (T1_le_B c (mem_subgroupOf.mp hy)))
  have h1 := card_dvd_of_le hle
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT1N).toEquiv] at h1

theorem not_mem_Z_of_mem_D (S : ZDSetup X Z M) {t : X} (htM : t ∉ M) {y : X}
    (hy : y ∈ M ⊓ conjugate M t) : y ∉ Z := by
  intro hyZ
  have h1 : t * y * t⁻¹ ∈ M := mem_conjugate_iff.mp (mem_inf.mp hy).2
  have h2 : t * y * t⁻¹ ∈ Z := by
    have := S.invariant.2 y hyZ t⁻¹
    rwa [inv_inv] at this
  apply htM
  refine S.prodDisc.mem_of_conj_mem h2 h1 (g := t) ?_
  have e : t⁻¹ * (t * y * t⁻¹) * t = y := by group
  rw [e]
  exact (mem_inf.mp hy).1

theorem card_P_mul_le_T1 (S : ZDSetup X Z M) (c : Conf16 Z M) {n i e : ℕ}
    (hB : BenderSub Z M c.B0 n i e) {S' : Subgroup X} (hS'D : S' ≤ c.D) (hS'2 : IsPGroup 2 S')
    (hS'u : ∀ y ∈ S', y * c.u = c.u * y) :
    Nat.card c.P * Nat.card S' ≤ Nat.card c.T1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS'BM : S' ≤ c.B ⊓ M := fun y hy =>
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (hS'u y hy), (mem_inf.mp (hS'D hy)).1⟩
  obtain ⟨g, -, hgle⟩ := exists_conjugate_le_of_isSylowOf c.hT1 hS'BM hS'2
  have hinter : ∀ x ∈ c.P, x ∈ conjugate S' g → x = 1 := by
    intro x hxP hxS
    by_contra hx1
    set H := c.P ⊓ conjugate S' g with hH
    have hH2 : IsPGroup 2 H := c.hP.isPGroup.to_le inf_le_left
    obtain ⟨k, hk⟩ := hH2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hx1
      have hbot : H = ⊥ := Subgroup.card_eq_one.mp (by rw [hk, pow_zero])
      have : x ∈ H := mem_inf.mpr ⟨hxP, hxS⟩
      rw [hbot, mem_bot] at this
      exact this
    have h2 : 2 ∣ Nat.card H := by rw [hk]; exact dvd_pow_self 2 hk0
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 2 h2
    have hyo : orderOf (y : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hy
    obtain ⟨hyP, hyS⟩ := mem_inf.mp y.2
    have hyZ : (y : X) ∈ Z := hB.invol _ (mem_inf.mp (c.hP.le hyP)).1 hyo
    have hgy : g * (y : X) * g⁻¹ ∈ S' := mem_conjugate_iff.mp hyS
    have hgyZ : g * (y : X) * g⁻¹ ∈ Z := by
      have := S.invariant.2 _ hyZ g⁻¹
      rwa [inv_inv] at this
    exact not_mem_Z_of_mem_D S c.htM (hS'D hgy) hgyZ
  let f : ↥c.P × ↥(conjugate S' g) → ↥c.T1 := fun p =>
    ⟨(p.1 : X) * p.2, mul_mem (c.hPT1 p.1.2) (hgle p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨p, s⟩ ⟨p', s'⟩ h
    have h' : (p : X) * s = p' * s' := congrArg Subtype.val h
    have e : (p' : X)⁻¹ * p = s' * (s : X)⁻¹ := by
      calc (p' : X)⁻¹ * p = (p' : X)⁻¹ * (p * s) * (s : X)⁻¹ := by group
        _ = (p' : X)⁻¹ * (p' * s') * (s : X)⁻¹ := by rw [h']
        _ = s' * (s : X)⁻¹ := by group
    have h1 : (p' : X)⁻¹ * p = 1 :=
      hinter _ (mul_mem (inv_mem p'.2) p.2) (by rw [e]; exact mul_mem s'.2 (inv_mem s.2))
    have hp : p = p' := Subtype.ext (inv_mul_eq_one.mp h1).symm
    have hs : s = s' := Subtype.ext (by
      rw [hp] at h'
      exact mul_left_cancel h')
    rw [hp, hs]
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at hcard
  have hconjcard : Nat.card (conjugate S' g) = Nat.card S' := by
    rw [conjugate]
    exact card_map_of_injective (MulAut.conj g⁻¹).injective
  rwa [hconjcard] at hcard

end Sec164

theorem ZDSetup.lemma164c
    (S : ZDSetup X Z M) (h162 : Lemma162Stmt Z M) (h163 : Lemma163Stmt Z M)
    (c : Conf16 Z M) {n i e : ℕ} (hB : BenderSub Z M (cenHull Z c.u) n i e)
    (hS : ∃ S' : Subgroup X, ABGLocalTools.IsSylowOf 2 S' c.D ∧ c.u ∈ S' ∧
      ∀ y ∈ S', y * c.u = c.u * y)
    (hconj : IsConj c.u (c.u * c.z)) :
    2 ^ n * Nat.card c.P ∣ (omega M).ncard - 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hS', -, hS'u⟩ := hS
  have hN := Sec164.dvd_card_normalizer_Qu S h162 h163 c hB hconj
  have hNM := card_dvd_of_le (Sec164.normalizer_Qu_le_M S h162 c hB)
  have hM := S.ncard_omega_sub_one_mul_card c.htM
  have hT := Sec164.card_P_mul_le_T1 S c hB hS'.le hS'.isPGroup hS'u
  obtain ⟨a, ha⟩ := c.hP.isPGroup.exists_card_eq
  obtain ⟨b, hb⟩ := c.hT1.isPGroup.exists_card_eq
  have hS'card := hS'.card_eq
  set k := (Nat.card ↥c.D).factorization 2 with hk
  have hab : a + k ≤ b := by
    rw [ha, hS'card, hb, ← pow_add] at hT
    by_contra hlt
    push Not at hlt
    have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hlt
    omega
  have hdvdM : 2 ^ n * (2 ^ a * 2 ^ k) ∣ Nat.card M := by
    refine dvd_trans ?_ (hN.trans hNM)
    refine mul_dvd_mul_left _ ?_
    rw [hb, ← pow_add]
    exact pow_dvd_pow 2 hab
  have hdvd1 : 2 ^ n * (2 ^ a * 2 ^ k) ∣
      ((omega M).ncard - 1) * (2 ^ k * (Nat.card ↥c.D / 2 ^ k)) := by
    rw [hk, Nat.ordProj_mul_ordCompl_eq_self]
    exact hdvdM.trans (dvd_of_eq hM.symm)
  have hD0 : Nat.card ↥c.D ≠ 0 := Nat.card_pos.ne'
  have hcop : Nat.Coprime (2 ^ n * 2 ^ a) (Nat.card ↥c.D / 2 ^ k) := by
    rw [← pow_add, hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl Nat.prime_two hD0)
  have hdvd2 : 2 ^ n * 2 ^ a ∣ ((omega M).ncard - 1) * (Nat.card ↥c.D / 2 ^ k) := by
    have e : 2 ^ n * (2 ^ a * 2 ^ k) = (2 ^ n * 2 ^ a) * 2 ^ k := by ring
    have e' : ((omega M).ncard - 1) * (2 ^ k * (Nat.card ↥c.D / 2 ^ k)) =
        (((omega M).ncard - 1) * (Nat.card ↥c.D / 2 ^ k)) * 2 ^ k := by ring
    rw [e, e'] at hdvd1
    exact Nat.dvd_of_mul_dvd_mul_right (by positivity) hdvd1
  rw [ha]
  exact hcop.dvd_of_dvd_mul_right hdvd2

end CFSG.GH74.Uniqueness
