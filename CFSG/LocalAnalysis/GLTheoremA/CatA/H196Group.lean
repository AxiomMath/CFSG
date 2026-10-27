module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.BorelTitsConstrained
public import CFSG.GroupTheory.ThompsonAxB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H196Facts
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.RadicalQuot

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.YS08
open CFSG.HardMathSupport.Solomon.Coordinator (IsChevOfChar)
open CFSG.Yardstones.Md0ec50421ce4 (catalogIs ambiguousChev)

variable {Y : Type} [Group Y]

@[expose] def conjSubEquiv (M : Subgroup Y) (g : Y) (h1 : ∀ m ∈ M, g * m * g⁻¹ ∈ M)
    (h2 : ∀ m ∈ M, g⁻¹ * m * g ∈ M) : ↥M ≃* ↥M where
  toFun m := ⟨g * m * g⁻¹, h1 m m.2⟩
  invFun m := ⟨g⁻¹ * m * g, h2 m m.2⟩
  left_inv m := Subtype.ext (by simp [mul_assoc])
  right_inv m := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjSubEquiv_val (M : Subgroup Y) (g : Y) (h1 : ∀ m ∈ M, g * m * g⁻¹ ∈ M)
    (h2 : ∀ m ∈ M, g⁻¹ * m * g ∈ M) (m : ↥M) :
    ((conjSubEquiv M g h1 h2 m : ↥M) : Y) = g * (m : Y) * g⁻¹ := rfl

theorem conj_mem_pCoreOf (p : ℕ) (M : Subgroup Y) (g : Y) (h1 : ∀ m ∈ M, g * m * g⁻¹ ∈ M)
    (h2 : ∀ m ∈ M, g⁻¹ * m * g ∈ M) {r : Y} (hr : r ∈ pCoreOf p M) :
    g * r * g⁻¹ ∈ pCoreOf p M := by
  obtain ⟨x, hx, hxr⟩ := Subgroup.mem_map.1 hr
  set e := conjSubEquiv M g h1 h2 with he
  have hTn : ((CFSG.pCore p ↥M).map e.toMonoidHom).Normal :=
    (CFSG.pCore_normal (p := p) (G := ↥M)).map e.toMonoidHom e.surjective
  have hTp : IsPGroup p ↥((CFSG.pCore p ↥M).map e.toMonoidHom) :=
    CFSG.pCore_isPGroup.map e.toMonoidHom
  have hTle : (CFSG.pCore p ↥M).map e.toMonoidHom ≤ CFSG.pCore p ↥M :=
    le_sSup ⟨hTn, hTp⟩
  have hmem : e x ∈ CFSG.pCore p ↥M :=
    hTle (Subgroup.mem_map_of_mem _ hx)
  refine Subgroup.mem_map.2 ⟨e x, hmem, ?_⟩
  rw [← hxr]
  simp [he, conjSubEquiv_val]

theorem pCoreOf_isPGroup (p : ℕ) (M : Subgroup Y) : IsPGroup p ↥(pCoreOf p M) :=
  CFSG.pCore_isPGroup.map M.subtype

theorem pCoreOf_le (p : ℕ) (M : Subgroup Y) : pCoreOf p M ≤ M :=
  Subgroup.map_subtype_le _

theorem eq_one_of_mem_of_not_dvd {p : ℕ} [hp : Fact p.Prime] {H K : Subgroup Y}
    (hH : IsPGroup p ↥H) (hK : ¬ p ∣ Nat.card ↥K) {k : Y} (hkH : k ∈ H) (hkK : k ∈ K) :
    k = 1 := by
  obtain ⟨n, hn⟩ := hH ⟨k, hkH⟩
  have hordH : orderOf (⟨k, hkH⟩ : ↥H) ∣ p ^ n := orderOf_dvd_of_pow_eq_one hn
  have hordK : orderOf (⟨k, hkK⟩ : ↥K) ∣ Nat.card ↥K := orderOf_dvd_natCard _
  have heqH : orderOf (⟨k, hkH⟩ : ↥H) = orderOf k := (Subgroup.orderOf_coe _).symm
  have heqK : orderOf (⟨k, hkK⟩ : ↥K) = orderOf k := (Subgroup.orderOf_coe _).symm
  have hcop : Nat.Coprime (orderOf k) p := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 ?_)
    intro hdvd
    apply hK
    exact dvd_trans (heqK ▸ hdvd) hordK
  have h1 : orderOf k = 1 :=
    (Nat.Coprime.pow_right n hcop).eq_one_of_dvd (heqH ▸ hordH)
  exact orderOf_eq_one_iff.1 h1

@[expose] def H196LQ (p : ℕ) (H S : Subgroup Y) : Prop :=
  ∀ Q : Subgroup Y, Q ≤ S → Q ≠ ⊥ → IsPGroup p ↥Q →
    ∀ h ∈ H ⊓ Subgroup.normalizer (Q : Set Y),
      (∀ r ∈ pCoreOf p (H ⊓ Subgroup.normalizer (Q : Set Y)), h * r = r * h) →
        h ∈ pCoreOf p (H ⊓ Subgroup.normalizer (Q : Set Y))

theorem mem_normalizer_subgroupOf_iff {H Q : Subgroup Y} (hQH : Q ≤ H) (n : ↥H) :
    n ∈ Subgroup.normalizer ((Q.subgroupOf H : Subgroup ↥H) : Set ↥H) ↔
      (n : Y) ∈ Subgroup.normalizer (Q : Set Y) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hx y
    by_cases hy : y ∈ H
    · have := hx ⟨y, hy⟩
      simpa [Subgroup.mem_subgroupOf] using this
    · have hyQ : y ∉ Q := fun h => hy (hQH h)
      have hnyQ : (n : Y) * y * (n : Y)⁻¹ ∉ Q := by
        intro h
        apply hy
        have h2 : y = (n : Y)⁻¹ * ((n : Y) * y * (n : Y)⁻¹) * (n : Y) := by group
        rw [h2]
        exact H.mul_mem (H.mul_mem (H.inv_mem n.2) (hQH h)) n.2
      exact ⟨fun h => absurd h hyQ, fun h => absurd h hnyQ⟩
  · intro hx x
    have := hx x
    simpa [Subgroup.mem_subgroupOf] using this

theorem mem_pCoreOf_of_mem_pCoreOf_subgroupOf {p : ℕ} {H M : Subgroup Y} (N' : Subgroup ↥H)
    (hM : ∀ n ∈ N', (n : Y) ∈ M) (hsurj : ∀ m ∈ M, ∃ n ∈ N', (n : Y) = m)
    {x : ↥H} (hx : x ∈ pCoreOf p N') : (x : Y) ∈ pCoreOf p M := by
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
  let φ : ↥N' →* ↥M :=
    { toFun := fun n => ⟨(n : Y), hM n n.2⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  have hφs : Function.Surjective φ := by
    intro m
    obtain ⟨n, hn, hnm⟩ := hsurj m m.2
    exact ⟨⟨n, hn⟩, Subtype.ext hnm⟩
  have hTn : ((CFSG.pCore p ↥N').map φ).Normal :=
    (CFSG.pCore_normal (p := p) (G := ↥N')).map φ hφs
  have hTp : IsPGroup p ↥((CFSG.pCore p ↥N').map φ) :=
    CFSG.pCore_isPGroup.map φ
  have hTle : (CFSG.pCore p ↥N').map φ ≤ CFSG.pCore p ↥M :=
    le_sSup ⟨hTn, hTp⟩
  refine Subgroup.mem_map.2 ⟨φ y, hTle (Subgroup.mem_map_of_mem _ hy), ?_⟩
  rw [← hyx]
  rfl

theorem h196LQ_of_lieQConstrained {p : ℕ} [Finite Y] (hL : LieQConstrained p) {H S : Subgroup Y}
    (hSH : S ≤ H) (hSn : (S.subgroupOf H).Normal) (hsimp : IsSimpleGroup ↥(S.subgroupOf H))
    (hna : ∃ a b : ↥(S.subgroupOf H), a * b ≠ b * a)
    (hchev : IsChevOfChar p ↥(S.subgroupOf H))
    (hcent : ∀ h ∈ H, (∀ s ∈ S, h * s = s * h) → h = 1) :
    H196LQ p H S := by
  intro Q hQS hQ1 hQp h hh hcomm
  have hQH : Q ≤ H := hQS.trans hSH
  set S' : Subgroup ↥H := S.subgroupOf H with hS'
  set Q' : Subgroup ↥H := Q.subgroupOf H with hQ'
  have hQ'S : Q' ≤ S' := by
    intro x hx
    rw [hS', Subgroup.mem_subgroupOf]
    exact hQS (Subgroup.mem_subgroupOf.1 hx)
  have hQ'1 : Q' ≠ ⊥ := by
    intro hbot
    apply hQ1
    rw [eq_bot_iff]
    intro q hq
    have hmem : (⟨q, hQH hq⟩ : ↥H) ∈ Q' := Subgroup.mem_subgroupOf.2 hq
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hmem)
  have hQ'p : IsPGroup p ↥Q' := hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  have hcent' : Subgroup.centralizer ((S' : Subgroup ↥H) : Set ↥H) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx
    have hxH : (x : Y) ∈ H := x.2
    have := hcent (x : Y) hxH (fun s hs => by
      have hsS' : (⟨s, hSH hs⟩ : ↥H) ∈ S' := Subgroup.mem_subgroupOf.2 hs
      have := hx ⟨s, hSH hs⟩ hsS'
      have := congrArg Subtype.val this
      simpa using this.symm)
    exact Subgroup.mem_bot.2 (Subtype.ext (by simpa using this))
  have key := hL ↥H S' hSn hsimp hna hchev hcent' Q' hQ'S hQ'1 hQ'p
  have hH' : (⟨h, hh.1⟩ : ↥H) ∈ Subgroup.normalizer ((Q' : Subgroup ↥H) : Set ↥H) :=
    (mem_normalizer_subgroupOf_iff hQH _).2 hh.2
  have hMsub : ∀ n ∈ Subgroup.normalizer ((Q' : Subgroup ↥H) : Set ↥H),
      (n : Y) ∈ H ⊓ Subgroup.normalizer (Q : Set Y) :=
    fun n hn => ⟨n.2, (mem_normalizer_subgroupOf_iff hQH n).1 hn⟩
  have hMsurj : ∀ m ∈ H ⊓ Subgroup.normalizer (Q : Set Y), ∃ n ∈ Subgroup.normalizer
      ((Q' : Subgroup ↥H) : Set ↥H), (n : Y) = m := fun m hm =>
    ⟨⟨m, hm.1⟩, (mem_normalizer_subgroupOf_iff hQH _).2 hm.2, rfl⟩
  have hcomm' : ∀ r' ∈ pCoreOf p (Subgroup.normalizer ((Q' : Subgroup ↥H) : Set ↥H)),
      (⟨h, hh.1⟩ : ↥H) * r' = r' * (⟨h, hh.1⟩ : ↥H) := by
    intro r' hr'
    have hrY := mem_pCoreOf_of_mem_pCoreOf_subgroupOf _ hMsub hMsurj hr'
    apply Subtype.ext
    exact hcomm _ hrY
  have hfin := key (⟨h, hh.1⟩ : ↥H) hH' hcomm'
  have := mem_pCoreOf_of_mem_pCoreOf_subgroupOf _ hMsub hMsurj hfin
  exact this

theorem h196LQ_of_ambLQ {p : ℕ} [Finite Y] (hA : I196AmbLQ p) {H S : Subgroup Y}
    (hSH : S ≤ H) (hSn : (S.subgroupOf H).Normal) (hsimp : IsSimpleGroup ↥(S.subgroupOf H))
    (hna : ∃ a b : ↥(S.subgroupOf H), a * b ≠ b * a)
    (hamb : catalogIs ↥(S.subgroupOf H) (ambiguousChev p))
    (hcent : ∀ h ∈ H, (∀ s ∈ S, h * s = s * h) → h = 1) :
    H196LQ p H S := by
  intro Q hQS hQ1 hQp h hh hcomm
  have hQH : Q ≤ H := hQS.trans hSH
  set S' : Subgroup ↥H := S.subgroupOf H with hS'
  set Q' : Subgroup ↥H := Q.subgroupOf H with hQ'
  have hQ'S : Q' ≤ S' := by
    intro x hx
    rw [hS', Subgroup.mem_subgroupOf]
    exact hQS (Subgroup.mem_subgroupOf.1 hx)
  have hQ'1 : Q' ≠ ⊥ := by
    intro hbot
    apply hQ1
    rw [eq_bot_iff]
    intro q hq
    have hmem : (⟨q, hQH hq⟩ : ↥H) ∈ Q' := Subgroup.mem_subgroupOf.2 hq
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hmem)
  have hQ'p : IsPGroup p ↥Q' := hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  have hcent' : Subgroup.centralizer ((S' : Subgroup ↥H) : Set ↥H) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx
    have hxH : (x : Y) ∈ H := x.2
    have := hcent (x : Y) hxH (fun s hs => by
      have hsS' : (⟨s, hSH hs⟩ : ↥H) ∈ S' := Subgroup.mem_subgroupOf.2 hs
      have := hx ⟨s, hSH hs⟩ hsS'
      have := congrArg Subtype.val this
      simpa using this.symm)
    exact Subgroup.mem_bot.2 (Subtype.ext (by simpa using this))
  have key := hA ↥H S' hSn hsimp hna hamb hcent' Q' hQ'S hQ'1 hQ'p
  have hH' : (⟨h, hh.1⟩ : ↥H) ∈ Subgroup.normalizer ((Q' : Subgroup ↥H) : Set ↥H) :=
    (mem_normalizer_subgroupOf_iff hQH _).2 hh.2
  have hMsub : ∀ n ∈ Subgroup.normalizer ((Q' : Subgroup ↥H) : Set ↥H),
      (n : Y) ∈ H ⊓ Subgroup.normalizer (Q : Set Y) :=
    fun n hn => ⟨n.2, (mem_normalizer_subgroupOf_iff hQH n).1 hn⟩
  have hMsurj : ∀ m ∈ H ⊓ Subgroup.normalizer (Q : Set Y), ∃ n ∈ Subgroup.normalizer
      ((Q' : Subgroup ↥H) : Set ↥H), (n : Y) = m := fun m hm =>
    ⟨⟨m, hm.1⟩, (mem_normalizer_subgroupOf_iff hQH _).2 hm.2, rfl⟩
  have hcomm' : ∀ r' ∈ pCoreOf p (Subgroup.normalizer ((Q' : Subgroup ↥H) : Set ↥H)),
      (⟨h, hh.1⟩ : ↥H) * r' = r' * (⟨h, hh.1⟩ : ↥H) := by
    intro r' hr'
    have hrY := mem_pCoreOf_of_mem_pCoreOf_subgroupOf _ hMsub hMsurj hr'
    apply Subtype.ext
    exact hcomm _ hrY
  have hfin := key (⟨h, hh.1⟩ : ↥H) hH' hcomm'
  have := mem_pCoreOf_of_mem_pCoreOf_subgroupOf _ hMsub hMsurj hfin
  exact this

theorem h196_core {p : ℕ} [hp : Fact p.Prime] [Finite Y] {H S : Subgroup Y}
    (hLQ : H196LQ p H S) {D : Subgroup Y} (hDp : IsPGroup p ↥D)
    (hDH : ∀ d ∈ D, ∀ h ∈ H, d * h * d⁻¹ ∈ H)
    {W : Subgroup Y} (hWC : W ≤ H ⊓ Subgroup.centralizer (D : Set Y))
    (hWn : ∀ c ∈ H ⊓ Subgroup.centralizer (D : Set Y), ∀ w ∈ W, c * w * c⁻¹ ∈ W)
    (hWp : ¬ p ∣ Nat.card ↥W)
    {Q : Subgroup Y} (hQS : Q ≤ S) (hQ1 : Q ≠ ⊥) (hQp : IsPGroup p ↥Q)
    (hQD : ∀ d ∈ D, ∀ x : Y, x ∈ Q ↔ d * x * d⁻¹ ∈ Q)
    (hWQ : ∀ w ∈ W, ∀ q ∈ Q, w * q = q * w) :
    W = ⊥ := by
  set M : Subgroup Y := H ⊓ Subgroup.normalizer (Q : Set Y) with hM
  set R : Subgroup Y := pCoreOf p M with hR
  have hRM : R ≤ M := pCoreOf_le p M
  have hMH : M ≤ H := inf_le_left
  have hDnQ : ∀ d ∈ D, d ∈ Subgroup.normalizer (Q : Set Y) := fun d hd =>
    Subgroup.mem_normalizer_iff.2 (fun x => hQD d hd x)
  have hDM : ∀ d ∈ D, ∀ m ∈ M, d * m * d⁻¹ ∈ M := by
    intro d hd m hm
    exact ⟨hDH d hd m hm.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hDnQ d hd) hm.2) (Subgroup.inv_mem _ (hDnQ d hd))⟩
  have hWconj : ∀ w ∈ W, ∀ x ∈ Q, w * x * w⁻¹ = x := by
    intro w hw x hx
    rw [hWQ w hw x hx]
    group
  have hWM : ∀ w ∈ W, w ∈ M := by
    intro w hw
    refine ⟨(hWC hw).1, Subgroup.mem_normalizer_iff.2 (fun x => ⟨fun hx => ?_, fun hy => ?_⟩)⟩
    · rw [hWconj w hw x hx]
      exact hx
    · have h1 : w⁻¹ * (w * x * w⁻¹) * w = x := by group
      have h2 := hWconj w⁻¹ (W.inv_mem hw) _ hy
      rw [inv_inv] at h2
      have hx' : x = w * x * w⁻¹ := h1.symm.trans h2
      rw [hx']
      exact hy
  have hWR : ∀ w ∈ W, ∀ r ∈ R, w * r * w⁻¹ ∈ R := by
    intro w hw r hr
    have h1 : ∀ m ∈ M, w * m * w⁻¹ ∈ M := fun m hm =>
      M.mul_mem (M.mul_mem (hWM w hw) hm) (M.inv_mem (hWM w hw))
    have h2 : ∀ m ∈ M, w⁻¹ * m * w ∈ M := fun m hm =>
      M.mul_mem (M.mul_mem (M.inv_mem (hWM w hw)) hm) (hWM w hw)
    exact conj_mem_pCoreOf p M w h1 h2 hr
  have hDR : ∀ d ∈ D, ∀ r ∈ R, d * r * d⁻¹ ∈ R := by
    intro d hd r hr
    have h2 : ∀ m ∈ M, d⁻¹ * m * d ∈ M := fun m hm => by
      simpa using hDM d⁻¹ (D.inv_mem hd) m hm
    exact conj_mem_pCoreOf p M d (hDM d hd) h2 hr
  have hWD : ∀ w ∈ W, ∀ d ∈ D, d * w = w * d := fun w hw d hd =>
    (Subgroup.mem_centralizer_iff.1 (hWC hw).2) d hd
  have hstep : ∀ r ∈ R, (∀ d ∈ D, d * r = r * d) → ∀ w ∈ W, r * w = w * r := by
    intro r hr hrD w hw
    have hrC : r ∈ H ⊓ Subgroup.centralizer (D : Set Y) :=
      ⟨hMH (hRM hr), Subgroup.mem_centralizer_iff.2 (fun d hd => hrD d hd)⟩
    have hk1 : r⁻¹ * w⁻¹ * r⁻¹⁻¹ ∈ W :=
      hWn r⁻¹ ((H ⊓ Subgroup.centralizer (D : Set Y)).inv_mem hrC) w⁻¹ (W.inv_mem hw)
    rw [inv_inv] at hk1
    have hkW : r⁻¹ * w⁻¹ * r * w ∈ W := W.mul_mem hk1 hw
    have hkR : r⁻¹ * w⁻¹ * r * w ∈ R := by
      have e : r⁻¹ * w⁻¹ * r * w = r⁻¹ * (w⁻¹ * r * w) := by group
      rw [e]
      have h3 : w⁻¹ * r * w ∈ R := by
        have := hWR w⁻¹ (W.inv_mem hw) r hr
        simpa using this
      exact R.mul_mem (R.inv_mem hr) h3
    have hk := eq_one_of_mem_of_not_dvd (pCoreOf_isPGroup p M) hWp hkR hkW
    have hcomm' : r⁻¹ * w⁻¹ = w⁻¹ * r⁻¹ := by
      rw [← commutatorElement_eq_one_iff_mul_comm]
      simpa [commutatorElement_def, mul_assoc] using hk
    have hinv := congrArg (fun z => z⁻¹) hcomm'
    simpa [mul_inv_rev] using hinv.symm
  let α : ↥W →* MulAut ↥R :=
    { toFun := fun w => conjSubEquiv R (w : Y) (fun r hr => hWR (w : Y) w.2 r hr)
        (fun r hr => by
          have := hWR (w : Y)⁻¹ (W.inv_mem w.2) r hr
          simpa using this)
      map_one' := by
        ext r
        simp [conjSubEquiv_val]
      map_mul' := fun a b => by
        ext r
        simp [conjSubEquiv_val, mul_assoc] }
  let β : ↥D →* MulAut ↥R :=
    { toFun := fun d => conjSubEquiv R (d : Y) (fun r hr => hDR (d : Y) d.2 r hr)
        (fun r hr => by
          have := hDR (d : Y)⁻¹ (D.inv_mem d.2) r hr
          simpa using this)
      map_one' := by
        ext r
        simp [conjSubEquiv_val]
      map_mul' := fun a b => by
        ext r
        simp [conjSubEquiv_val, mul_assoc] }
  have hcomm : ∀ (a : ↥W) (b : ↥D), α a * β b = β b * α a := by
    intro a b
    ext r
    have hab : (a : Y) * (b : Y) = (b : Y) * (a : Y) := (hWD a a.2 b b.2).symm
    simp only [MulAut.mul_apply, α, β, MonoidHom.coe_mk, OneHom.coe_mk, conjSubEquiv_val,
      Subgroup.coe_mul, Subgroup.coe_inv]
    rw [show (a : Y) * ((b : Y) * (r : Y) * (b : Y)⁻¹) * (a : Y)⁻¹
        = ((a : Y) * (b : Y)) * (r : Y) * ((a : Y) * (b : Y))⁻¹ by group,
      show (b : Y) * ((a : Y) * (r : Y) * (a : Y)⁻¹) * (b : Y)⁻¹
        = ((b : Y) * (a : Y)) * (r : Y) * ((b : Y) * (a : Y))⁻¹ by group, hab]
  have hfix : ∀ (a : ↥W) (r : ↥R), (∀ b : ↥D, β b r = r) → α a r = r := by
    intro a r hr
    have hrD : ∀ d ∈ D, d * (r : Y) = (r : Y) * d := by
      intro d hd
      have h := congrArg (fun z : ↥R => (z : Y)) (hr ⟨d, hd⟩)
      simp only [β, MonoidHom.coe_mk, OneHom.coe_mk, conjSubEquiv_val] at h
      calc d * (r : Y) = (d * (r : Y) * d⁻¹) * d := by group
        _ = (r : Y) * d := by rw [h]
    have hc := hstep (r : Y) r.2 hrD (a : Y) a.2
    apply Subtype.ext
    simp only [α, MonoidHom.coe_mk, OneHom.coe_mk, conjSubEquiv_val]
    calc (a : Y) * (r : Y) * (a : Y)⁻¹ = ((r : Y) * (a : Y)) * (a : Y)⁻¹ := by rw [hc]
      _ = (r : Y) := by group
  have hT := CFSG.GroupTheory.thompson_A_times_B (p := p) (pCoreOf_isPGroup p M) hWp hDp α β hcomm hfix
  have hWcent : ∀ w ∈ W, ∀ r ∈ R, w * r = r * w := by
    intro w hw r hr
    have h1 := congrArg (fun φ : MulAut ↥R => ((φ ⟨r, hr⟩ : ↥R) : Y)) (hT ⟨w, hw⟩)
    simp only [α, MonoidHom.coe_mk, OneHom.coe_mk, conjSubEquiv_val, MulAut.one_apply,
      Subgroup.coe_mk] at h1
    calc w * r = (w * r * w⁻¹) * w := by group
      _ = r * w := by rw [h1]
  have hWR' : W ≤ R := by
    intro w hw
    apply hLQ Q hQS hQ1 hQp w (hWM w hw)
    intro r hr
    exact hWcent w hw r hr
  rw [eq_bot_iff]
  intro w hw
  exact (Subgroup.mem_bot).2 (eq_one_of_mem_of_not_dvd (pCoreOf_isPGroup p M) hWp (hWR' hw) hw)

end CFSG.LocalAnalysis.GLTheoremA
