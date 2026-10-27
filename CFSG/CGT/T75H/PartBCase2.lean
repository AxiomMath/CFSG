module

public import CFSG.CGT.T75H.PartBCase2Core
public import CFSG.CGT.T75H.Endgame
public import CFSG.CGT.T75H.LocalAG
public import CFSG.CGT.T75H.PartBOdd

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.OddInversion
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

@[expose] def conjEquivOfInvol (W : Subgroup G) (u : G) (huu : u * u = 1)
    (hu : ∀ x ∈ W, u * x * u⁻¹ ∈ W) : W ≃* W where
  toFun m := ⟨u * m * u⁻¹, hu m m.2⟩
  invFun m := ⟨u * m * u⁻¹, hu m m.2⟩
  left_inv m := by
    apply Subtype.ext
    show u * (u * (m : G) * u⁻¹) * u⁻¹ = m
    calc u * (u * (m : G) * u⁻¹) * u⁻¹ = (u * u) * (m : G) * (u * u)⁻¹ := by group
      _ = m := by rw [huu]; group
  right_inv m := by
    apply Subtype.ext
    show u * (u * (m : G) * u⁻¹) * u⁻¹ = m
    calc u * (u * (m : G) * u⁻¹) * u⁻¹ = (u * u) * (m : G) * (u * u)⁻¹ := by group
      _ = m := by rw [huu]; group
  map_mul' a b := by
    apply Subtype.ext
    show u * ((a : G) * b) * u⁻¹ = (u * (a : G) * u⁻¹) * (u * (b : G) * u⁻¹)
    group

@[expose] def wSub (T₁ Q : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | ∃ q ∈ Q, ∃ t ∈ T₁, x = q⁻¹ * t * q}

theorem conj_mem_wSub {Q : Subgroup G} {q t : G} (hq : q ∈ Q) (ht : t ∈ T₁) :
    q⁻¹ * t * q ∈ wSub T₁ Q :=
  Subgroup.subset_closure ⟨q, hq, t, ht, rfl⟩

theorem T₁_le_wSub {Q : Subgroup G} : T₁ ≤ wSub T₁ Q := fun t ht => by
  have := conj_mem_wSub (T₁ := T₁) (Q.one_mem) ht
  simpa using this

theorem wSub_le_centralizer {Q : Subgroup G} {ε : G} (hQ : ∀ q ∈ Q, ε * q = q * ε)
    (hT : ∀ t ∈ T₁, ε * t = t * ε) : wSub T₁ Q ≤ Subgroup.centralizer ({ε} : Set G) := by
  rw [wSub, Subgroup.closure_le]
  rintro x ⟨q, hq, t, ht, rfl⟩
  refine Subgroup.mem_centralizer_singleton_iff.2 ?_
  have hqε := hQ q hq
  have hqinv : ε * q⁻¹ = q⁻¹ * ε := by
    calc ε * q⁻¹ = q⁻¹ * (q * ε) * q⁻¹ := by group
      _ = q⁻¹ * (ε * q) * q⁻¹ := by rw [hqε]
      _ = q⁻¹ * ε := by group
  calc q⁻¹ * t * q * ε = q⁻¹ * t * (q * ε) := by group
    _ = q⁻¹ * t * (ε * q) := by rw [hqε]
    _ = q⁻¹ * (t * ε) * q := by group
    _ = q⁻¹ * (ε * t) * q := by rw [hT t ht]
    _ = (q⁻¹ * ε) * t * q := by group
    _ = (ε * q⁻¹) * t * q := by rw [hqinv]
    _ = ε * (q⁻¹ * t * q) := by group

theorem wSub_conj_mem {Q : Subgroup G} {u : G} (hQu : ∀ q ∈ Q, u * q * u⁻¹ ∈ Q)
    (hTu : ∀ t ∈ T₁, u * t * u⁻¹ ∈ T₁) {x : G} (hx : x ∈ wSub T₁ Q) :
    u * x * u⁻¹ ∈ wSub T₁ Q := by
  refine conj_mem_closure_of (fun s hs => ?_) hx
  obtain ⟨q, hq, t, ht, rfl⟩ := hs
  have e : u * (q⁻¹ * t * q) * u⁻¹ = (u * q * u⁻¹)⁻¹ * (u * t * u⁻¹) * (u * q * u⁻¹) := by group
  rw [e]
  exact conj_mem_wSub (hQu q hq) (hTu t ht)

theorem normalClosure_subgroupOf_wSub {Q : Subgroup G} (hQW : Q ≤ wSub T₁ Q) :
    Subgroup.normalClosure ((T₁.subgroupOf (wSub T₁ Q) : Subgroup (wSub T₁ Q)) :
      Set (wSub T₁ Q)) = ⊤ := by
  classical
  set W := wSub T₁ Q with hW
  set K : Subgroup W := Subgroup.normalClosure ((T₁.subgroupOf W : Subgroup W) : Set W) with hK
  have hKn : K.Normal := Subgroup.normalClosure_normal
  have key : ∀ g (hg : g ∈ Subgroup.closure {x | ∃ q ∈ Q, ∃ t ∈ T₁, x = q⁻¹ * t * q}),
      ∃ hgW : g ∈ W, (⟨g, hgW⟩ : W) ∈ K := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨q, hq, t, ht, rfl⟩ := hs
      have hgW : q⁻¹ * t * q ∈ W := conj_mem_wSub hq ht
      refine ⟨hgW, ?_⟩
      have hqW : q ∈ W := hQW hq
      have htW : t ∈ W := T₁_le_wSub ht
      have hmem : (⟨t, htW⟩ : W) ∈ K :=
        Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.2 ht)
      have := hKn.conj_mem _ hmem ⟨q⁻¹, W.inv_mem hqW⟩
      convert this using 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    | one => exact ⟨W.one_mem, K.one_mem⟩
    | mul a b _ _ ha hb =>
      obtain ⟨haW, ha'⟩ := ha
      obtain ⟨hbW, hb'⟩ := hb
      exact ⟨W.mul_mem haW hbW, K.mul_mem ha' hb'⟩
    | inv a _ ha =>
      obtain ⟨haW, ha'⟩ := ha
      exact ⟨W.inv_mem haW, K.inv_mem ha'⟩
  rw [eq_top_iff]
  intro u _
  obtain ⟨hu, h⟩ := key u.1 u.2
  exact h

theorem case2_false [Finite G] [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a)
    (hInd : SimpleCaseUpTo (Nat.card G)) (h215 : Lemma215Stmt) (hI : ListWCIdentification)
    (hT : IsWC T) (hc4 : Nat.card T = 4) {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y)
    {N : Subgroup G} (hN : OddCore T T₁ N) (hN3 : IsPGroup 3 N) {e₁ e₂ : G}
    (he₁T₁ : ∀ t ∈ T₁, t * e₁ = e₁ * t) (he₂T₁ : ∀ t ∈ T₁, t * e₂ = e₂ * t)
    (he₁T : ∀ t ∈ T, t * e₁ = e₁ * t) (he₂T : ∀ t ∈ T, t * e₂ = e₂ * t)
    (he₁e₁ : e₁ * e₁ = 1) (he₂e₂ : e₂ * e₂ = 1) (he₁e₂ : e₁ * e₂ = e₂ * e₁) {m₁ m₂ : G}
    (hm₁N : m₁ ∈ N) (hm₂N : m₂ ∈ N) (hm₁1 : m₁ ≠ 1) (hm₂1 : m₂ ≠ 1)
    (hℓm₁ : ℓ * m₁ * ℓ⁻¹ = m₁⁻¹) (hℓm₂ : ℓ * m₂ * ℓ⁻¹ = m₂⁻¹)
    (h₁m₁ : e₁ * m₁ * e₁⁻¹ = m₁) (h₁m₂ : e₁ * m₂ * e₁⁻¹ = m₂⁻¹)
    (h₂m₂ : e₂ * m₂ * e₂⁻¹ = m₂) (h₂m₁ : e₂ * m₁ * e₂⁻¹ = m₁⁻¹) : False := by
  classical
  obtain ⟨x₁, hx₁S, hx₁⟩ := D.sec3.conj
  have hT₁wc : IsWC T₁ := hx₁ ▸ hT.conj x₁
  have hT₁ab := hT₁wc.1
  set Q : Subgroup G := Subgroup.closure ({m₁, m₂} : Set G) with hQdef
  have hm₁Q : m₁ ∈ Q := Subgroup.subset_closure (by simp)
  have hm₂Q : m₂ ∈ Q := Subgroup.subset_closure (by simp)
  have hQN : Q ≤ N := (Subgroup.closure_le N).2 (by
    rintro x (rfl | rfl)
    · exact hm₁N
    · exact hm₂N)
  have hinv1 : ∀ e : G, e * e = 1 → e⁻¹ = e := fun e h => inv_eq_of_mul_eq_one_right h
  have he₁inv := hinv1 e₁ he₁e₁
  have he₂inv := hinv1 e₂ he₂e₂
  have hℓinv : ℓ⁻¹ = ℓ := D.inv_ℓ
  have hℓe₁ : ℓ * e₁ = e₁ * ℓ := he₁T₁ ℓ D.hℓT₁
  have hℓe₂ : ℓ * e₂ = e₂ * ℓ := he₂T₁ ℓ D.hℓT₁
  set ε : G := ℓ * (e₁ * e₂) with hε
  have hℓε : ℓ * (e₁ * e₂) = (e₁ * e₂) * ℓ := by
    calc ℓ * (e₁ * e₂) = (ℓ * e₁) * e₂ := by group
      _ = (e₁ * ℓ) * e₂ := by rw [hℓe₁]
      _ = e₁ * (ℓ * e₂) := by group
      _ = e₁ * (e₂ * ℓ) := by rw [hℓe₂]
      _ = (e₁ * e₂) * ℓ := by group
  have hεε : ε * ε = 1 := by
    have h12 : (e₁ * e₂) * (e₁ * e₂) = 1 := by
      calc (e₁ * e₂) * (e₁ * e₂) = e₁ * (e₂ * e₁) * e₂ := by group
        _ = e₁ * (e₁ * e₂) * e₂ := by rw [he₁e₂]
        _ = (e₁ * e₁) * (e₂ * e₂) := by group
        _ = 1 := by rw [he₁e₁, he₂e₂, one_mul]
    calc ε * ε = ℓ * (e₁ * e₂) * (ℓ * (e₁ * e₂)) := by rw [hε]
      _ = ℓ * ((e₁ * e₂) * ℓ) * (e₁ * e₂) := by group
      _ = ℓ * (ℓ * (e₁ * e₂)) * (e₁ * e₂) := by rw [← hℓε]
      _ = (ℓ * ℓ) * ((e₁ * e₂) * (e₁ * e₂)) := by group
      _ = 1 := by rw [D.ℓℓ, h12, one_mul]
  have hε1 : ε ≠ 1 := by
    intro h
    have hℓ' : ℓ = (e₁ * e₂)⁻¹ := by
      have : ℓ * (e₁ * e₂) = 1 := h
      exact eq_inv_of_mul_eq_one_left this
    have hb1 : b * ℓ = ℓ * b := by
      have hcb : b * (e₁ * e₂)⁻¹ = (e₁ * e₂)⁻¹ * b := by
        have h1 : b * (e₁ * e₂) = (e₁ * e₂) * b := by
          calc b * (e₁ * e₂) = (b * e₁) * e₂ := by group
            _ = (e₁ * b) * e₂ := by rw [he₁T b D.hb]
            _ = e₁ * (b * e₂) := by group
            _ = e₁ * (e₂ * b) := by rw [he₂T b D.hb]
            _ = (e₁ * e₂) * b := by group
        calc b * (e₁ * e₂)⁻¹ = (e₁ * e₂)⁻¹ * ((e₁ * e₂) * b) * (e₁ * e₂)⁻¹ := by group
          _ = (e₁ * e₂)⁻¹ * (b * (e₁ * e₂)) * (e₁ * e₂)⁻¹ := by rw [h1]
          _ = (e₁ * e₂)⁻¹ * b := by group
      rw [hℓ']
      exact hcb
    have : ℓ * a = ℓ := by
      calc ℓ * a = b * ℓ * b := D.conj_ℓ_b.symm
        _ = ℓ * b * b := by rw [hb1]
        _ = ℓ := by rw [mul_assoc, D.bb, mul_one]
    exact D.ha1 (mul_left_cancel (this.trans (mul_one ℓ).symm))
  have hεm : ∀ m : G, ℓ * m * ℓ⁻¹ = m⁻¹ → ((e₁ * e₂) * m * (e₁ * e₂)⁻¹ = m⁻¹) → ε * m = m * ε := by
    intro m hm h12
    have : ε * m * ε⁻¹ = m := by
      calc ε * m * ε⁻¹ = ℓ * ((e₁ * e₂) * m * (e₁ * e₂)⁻¹) * ℓ⁻¹ := by rw [hε]; group
        _ = ℓ * m⁻¹ * ℓ⁻¹ := by rw [h12]
        _ = (ℓ * m * ℓ⁻¹)⁻¹ := by group
        _ = m := by rw [hm, inv_inv]
    exact mul_inv_eq_iff_eq_mul.1 this
  have h₁₂m₁ : (e₁ * e₂) * m₁ * (e₁ * e₂)⁻¹ = m₁⁻¹ := by
    calc (e₁ * e₂) * m₁ * (e₁ * e₂)⁻¹ = e₁ * (e₂ * m₁ * e₂⁻¹) * e₁⁻¹ := by group
      _ = e₁ * m₁⁻¹ * e₁⁻¹ := by rw [h₂m₁]
      _ = (e₁ * m₁ * e₁⁻¹)⁻¹ := by group
      _ = m₁⁻¹ := by rw [h₁m₁]
  have h₁₂m₂ : (e₁ * e₂) * m₂ * (e₁ * e₂)⁻¹ = m₂⁻¹ := by
    calc (e₁ * e₂) * m₂ * (e₁ * e₂)⁻¹ = e₁ * (e₂ * m₂ * e₂⁻¹) * e₁⁻¹ := by group
      _ = e₁ * m₂ * e₁⁻¹ := by rw [h₂m₂]
      _ = m₂⁻¹ := h₁m₂
  have hεm₁ : ε * m₁ = m₁ * ε := hεm m₁ hℓm₁ h₁₂m₁
  have hεm₂ : ε * m₂ = m₂ * ε := hεm m₂ hℓm₂ h₁₂m₂
  have hQε : ∀ q ∈ Q, ε * q = q * ε := by
    intro q hq
    induction hq using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hεm₁
      · exact hεm₂
    | one => simp
    | mul a b _ _ ha hb =>
      calc ε * (a * b) = (ε * a) * b := by group
        _ = (a * ε) * b := by rw [ha]
        _ = a * (ε * b) := by group
        _ = a * (b * ε) := by rw [hb]
        _ = (a * b) * ε := by group
    | inv a _ ha =>
      calc ε * a⁻¹ = a⁻¹ * (a * ε) * a⁻¹ := by group
        _ = a⁻¹ * (ε * a) * a⁻¹ := by rw [ha]
        _ = a⁻¹ * ε := by group
  have hT₁ε : ∀ t ∈ T₁, ε * t = t * ε := by
    intro t ht
    have htℓ : t * ℓ = ℓ * t := elemAbelian_mul_comm hT₁ab ht D.hℓT₁
    have h1 : t * (e₁ * e₂) = (e₁ * e₂) * t := by
      calc t * (e₁ * e₂) = (t * e₁) * e₂ := by group
        _ = (e₁ * t) * e₂ := by rw [he₁T₁ t ht]
        _ = e₁ * (t * e₂) := by group
        _ = e₁ * (e₂ * t) := by rw [he₂T₁ t ht]
        _ = (e₁ * e₂) * t := by group
    calc ε * t = ℓ * ((e₁ * e₂) * t) := by rw [hε]; group
      _ = ℓ * (t * (e₁ * e₂)) := by rw [h1]
      _ = (ℓ * t) * (e₁ * e₂) := by group
      _ = (t * ℓ) * (e₁ * e₂) := by rw [htℓ]
      _ = t * (ℓ * (e₁ * e₂)) := by group
  set W : Subgroup G := wSub T₁ Q with hW
  have hT₁W : T₁ ≤ W := T₁_le_wSub
  have hWε : W ≤ Subgroup.centralizer ({ε} : Set G) := wSub_le_centralizer hQε hT₁ε
  have hcard : Nat.card W < Nat.card G :=
    lt_of_le_of_lt (Subgroup.card_le_of_le hWε) (card_centralizer_lt hna hε1)
  have hmW : ∀ m ∈ Q, m ∈ N → ℓ * m * ℓ⁻¹ = m⁻¹ → m ∈ W := by
    intro m hmQ hmN hm
    have hmm : m * m ∈ W := by
      rw [← mul_conj_eq_sq D.ℓℓ hm]
      exact W.mul_mem (hT₁W D.hℓT₁) (conj_mem_wSub hmQ D.hℓT₁)
    have h3 : (⟨m, hmN⟩ : N) ^ 2 ∈ W.subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]
      simpa [sq] using hmm
    exact Subgroup.mem_subgroupOf.1 (mem_of_sq_mem (p := 3) (by norm_num) hN3 h3)
  have hm₁W : m₁ ∈ W := hmW m₁ hm₁Q hm₁N hℓm₁
  have hm₂W : m₂ ∈ W := hmW m₂ hm₂Q hm₂N hℓm₂
  have hQW : Q ≤ W := (Subgroup.closure_le W).2 (by
    rintro x (rfl | rfl)
    · exact hm₁W
    · exact hm₂W)
  have hQa : ∀ q ∈ Q, a * q * a⁻¹ ∈ Q := by
    intro q hq
    have h := Subgroup.mem_centralizer_iff.1 (hN.le_centralizer (hQN hq)) a D.haT
    have e : a * q * a⁻¹ = q := by rw [h]; group
    rw [e]
    exact hq
  have hTa : ∀ t ∈ T₁, a * t * a⁻¹ ∈ T₁ := fun t ht =>
    Timmesfeld75.conj_mem_of_mem_normalizer D.haN ht
  have hQe₁ : ∀ q ∈ Q, e₁ * q * e₁⁻¹ ∈ Q := fun q hq =>
    conj_mem_closure_of (fun s hs => by
      rcases hs with rfl | rfl
      · rw [h₁m₁]; exact hm₁Q
      · rw [h₁m₂]; exact Q.inv_mem hm₂Q) hq
  have hQe₂ : ∀ q ∈ Q, e₂ * q * e₂⁻¹ ∈ Q := fun q hq =>
    conj_mem_closure_of (fun s hs => by
      rcases hs with rfl | rfl
      · rw [h₂m₁]; exact Q.inv_mem hm₁Q
      · rw [h₂m₂]; exact hm₂Q) hq
  have hTe₁ : ∀ t ∈ T₁, e₁ * t * e₁⁻¹ ∈ T₁ := fun t ht => by
    have e : e₁ * t * e₁⁻¹ = t := by rw [← he₁T₁ t ht]; group
    rw [e]; exact ht
  have hTe₂ : ∀ t ∈ T₁, e₂ * t * e₂⁻¹ ∈ T₁ := fun t ht => by
    have e : e₂ * t * e₂⁻¹ = t := by rw [← he₂T₁ t ht]; group
    rw [e]; exact ht
  have hWa : ∀ x ∈ W, a * x * a⁻¹ ∈ W := fun x hx => wSub_conj_mem hQa hTa hx
  have hWe₁ : ∀ x ∈ W, e₁ * x * e₁⁻¹ ∈ W := fun x hx => wSub_conj_mem hQe₁ hTe₁ hx
  have hWe₂ : ∀ x ∈ W, e₂ * x * e₂⁻¹ ∈ W := fun x hx => wSub_conj_mem hQe₂ hTe₂ hx
  let φa := conjEquivOfInvol W a D.aa hWa
  let φ₁ := conjEquivOfInvol W e₁ he₁e₁ hWe₁
  let φ₂ := conjEquivOfInvol W e₂ he₂e₂ hWe₂
  have hℓW : ℓ ∈ W := hT₁W D.hℓT₁
  have hyW : y ∈ W := hT₁W D.hy
  let ℓ' : W := ⟨ℓ, hℓW⟩
  let y' : W := ⟨y, hyW⟩
  let m₁' : W := ⟨m₁, hm₁W⟩
  let m₂' : W := ⟨m₂, hm₂W⟩
  have hy1 : y ≠ 1 := fun h => D.hyL (h ▸ (normIn T₁ T).one_mem)
  have hyℓ : y ≠ ℓ := fun h => D.hyL (h ▸ D.hℓ)
  have hcomm_a : ∀ m ∈ N, a * m * a⁻¹ = m := fun m hm => by
    have h := Subgroup.mem_centralizer_iff.1 (hN.le_centralizer hm) a D.haT
    rw [h]; group
  have hT₁card : Nat.card T₁ = 4 := by rw [hx₁, card_conjSubgroup, hc4]
  have h4 : Nat.card (T₁.subgroupOf W) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₁W).toEquiv, hT₁card]
  have hQ' : ∀ x ∈ Subgroup.closure ({m₁', m₂'} : Set W), ∃ k : ℕ, x ^ (3 ^ k) = 1 := by
    intro x hx
    have hxQ : (x : G) ∈ Q := by
      induction hx using Subgroup.closure_induction with
      | mem s hs =>
        rcases hs with rfl | rfl
        · exact hm₁Q
        · exact hm₂Q
      | one => exact Q.one_mem
      | mul a b _ _ ha hb => exact Q.mul_mem ha hb
      | inv a _ ha => exact Q.inv_mem ha
    obtain ⟨k, hk⟩ := hN3 ⟨x, hQN hxQ⟩
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  exact case2_core (R := W) hInd h215 hI hcard (isWC_subgroupOf hT₁wc W hT₁W)
    (normalClosure_subgroupOf_wSub hQW) h4 (ℓ := ℓ') (y := y')
    (Subgroup.mem_subgroupOf.2 D.hℓT₁) (Subgroup.mem_subgroupOf.2 D.hy)
    (Subtype.ext D.ℓℓ) (Subtype.ext D.yy) (fun h => D.hℓ1 (congrArg Subtype.val h))
    (fun h => hy1 (congrArg Subtype.val h)) (fun h => hyℓ (congrArg Subtype.val h))
    (Subtype.ext (elemAbelian_mul_comm hT₁ab D.hℓT₁ D.hy))
    (fun t ht => by
      rcases D.hT₁ (t : G) (Subgroup.mem_subgroupOf.1 ht) with h | h | h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
      · exact Or.inr (Or.inr (Or.inr (Subtype.ext h))))
    φa φ₁ φ₂
    (Subtype.ext (by
      show a * ℓ * a⁻¹ = ℓ
      rw [D.comm_aℓ]; group))
    (Subtype.ext (by
      show a * y * a⁻¹ = y * ℓ
      rw [D.inv_a]; exact D.conj_a_y))
    (m₁ := m₁') (m₂ := m₂') (fun h => hm₁1 (congrArg Subtype.val h))
    (fun h => hm₂1 (congrArg Subtype.val h)) hQ'
    (Subtype.ext hℓm₁) (Subtype.ext hℓm₂)
    (Subtype.ext (hcomm_a m₁ hm₁N)) (Subtype.ext (hcomm_a m₂ hm₂N))
    (Subtype.ext h₁m₁) (Subtype.ext h₁m₂) (Subtype.ext h₂m₂) (Subtype.ext h₂m₁)

end CFSG.CGT.T75H
