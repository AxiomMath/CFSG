module

public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving Subgroup

variable {G : Type*} [Group G]

theorem inv_of_fixedPointFree_involution [Finite G] {α : G} (hα : α * α = 1) {Q : Subgroup G}
    (hQ : ∀ q ∈ Q, α * q * α⁻¹ ∈ Q) (hfix : ∀ q ∈ Q, α * q * α⁻¹ = q → q = 1) :
    ∀ q ∈ Q, α * q * α⁻¹ = q⁻¹ := by
  have key : ∀ y : G, α * (α * y * α⁻¹) * α⁻¹ = y := fun y => by
    calc α * (α * y * α⁻¹) * α⁻¹ = (α * α) * y * (α⁻¹ * α⁻¹) := by group
      _ = y := by
        rw [hα, show α⁻¹ * α⁻¹ = (α * α)⁻¹ by group, hα]
        group
  let f : Q → Q := fun q => ⟨(q : G)⁻¹ * (α * q * α⁻¹), Q.mul_mem (Q.inv_mem q.2) (hQ q q.2)⟩
  have hinj : Function.Injective f := by
    intro q r h
    have h' : (q : G)⁻¹ * (α * q * α⁻¹) = (r : G)⁻¹ * (α * r * α⁻¹) := congrArg Subtype.val h
    have e1 : α * (r : G) * α⁻¹ = r * ((q : G)⁻¹ * (α * q * α⁻¹)) := by
      calc α * (r : G) * α⁻¹ = r * ((r : G)⁻¹ * (α * r * α⁻¹)) := by group
        _ = r * ((q : G)⁻¹ * (α * q * α⁻¹)) := by rw [← h']
    have hw : α * ((r : G) * (q : G)⁻¹) * α⁻¹ = (r : G) * (q : G)⁻¹ := by
      calc α * ((r : G) * (q : G)⁻¹) * α⁻¹ = (α * r * α⁻¹) * (α * q * α⁻¹)⁻¹ := by group
        _ = r * ((q : G)⁻¹ * (α * q * α⁻¹)) * (α * q * α⁻¹)⁻¹ := by rw [e1]
        _ = r * (q : G)⁻¹ := by group
    have := hfix _ (Q.mul_mem r.2 (Q.inv_mem q.2)) hw
    exact Subtype.ext (mul_inv_eq_one.1 this).symm
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.1 hinj
  intro q hq
  obtain ⟨x, hx⟩ := hsurj ⟨q, hq⟩
  have hq' : q = (x : G)⁻¹ * (α * x * α⁻¹) := (congrArg Subtype.val hx).symm
  calc α * q * α⁻¹ = (α * (x : G)⁻¹ * α⁻¹) * (α * (α * x * α⁻¹) * α⁻¹) := by rw [hq']; group
    _ = (α * (x : G)⁻¹ * α⁻¹) * x := by rw [key]
    _ = q⁻¹ := by rw [hq']; group

theorem isConj_mul_of_inverts_odd {α a : G} (ha : α * a * α⁻¹ = a⁻¹)
    (hodd : Odd (orderOf a)) : IsConj α (a * α) := by
  obtain ⟨m, hm⟩ := hodd
  set x : G := a ^ (m + 1) with hx
  have hxx : x * x = a := by
    have h1 : a ^ (orderOf a) = 1 := pow_orderOf_eq_one a
    calc x * x = a ^ (m + 1) * a ^ (m + 1) := rfl
      _ = a ^ (2 * m + 1) * a := by rw [← pow_add, ← pow_succ]; ring_nf
      _ = a := by rw [← hm, h1, one_mul]
  have hαx : α * x * α⁻¹ = x⁻¹ := by
    have := conj_zpow (a := α) (b := a) (i := ((m + 1 : ℕ) : ℤ))
    rw [ha, zpow_natCast, zpow_natCast, inv_pow] at this
    exact this.symm.trans (by rfl)
  have hαx' : α * x⁻¹ * α⁻¹ = x := by
    have := conj_inv (a := x) (b := α)
    rw [hαx, inv_inv] at this
    exact this.symm
  refine isConj_iff.2 ⟨x, ?_⟩
  calc x * α * x⁻¹ = x * (α * x⁻¹ * α⁻¹) * α := by group
    _ = x * x * α := by rw [hαx']
    _ = a * α := by rw [hxx]

theorem gLAPPrimeCoreOf_centralizer_eq_bot_of_inverting_involution [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {α s : G} (hα : α * α = 1) (hs : orderOf s = p)
    (hinv : α * s * α⁻¹ = s⁻¹)
    (hL : GLAPPrimeCoreOf p (Subgroup.centralizer ({α} : Set G) ⊓
      Subgroup.centralizer ({s} : Set G)) = ⊥)
    (hbd : ∀ x y : G, IsConj α x → IsConj α y → orderOf (x * y) ≤ 6) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)) = ⊥ := by
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα
  set C := Subgroup.centralizer ({s} : Set G) with hC
  set Q := GLAPPrimeCoreOf p C with hQ
  have hQC : Q ≤ C := GLAPPrimeCoreOf_le C
  have hcop : Nat.Coprime p (Nat.card Q) := coprime_card_GLAPPrimeCoreOf hp C
  have hαC : ∀ g ∈ C, α * g * α⁻¹ ∈ C := by
    intro g hg
    rw [hC, Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    have hinv' : α * s⁻¹ * α⁻¹ = s := by
      have := conj_inv (a := s) (b := α)
      rw [hinv, inv_inv] at this
      exact this.symm
    calc α * g * α⁻¹ * s = α * g * α⁻¹ * (α * s⁻¹ * α⁻¹) := by rw [hinv']
      _ = α * (g * s⁻¹) * α⁻¹ := by group
      _ = α * (s⁻¹ * g) * α⁻¹ := by
        rw [(Commute.inv_right (show Commute g s from hg)).eq]
      _ = (α * s⁻¹ * α⁻¹) * (α * g * α⁻¹) := by group
      _ = s * (α * g * α⁻¹) := by rw [hinv']
  have hQα : ∀ q ∈ Q, α * q * α⁻¹ ∈ Q := by
    set S : Subgroup G := Q.map (MulAut.conj α).toMonoidHom with hS
    have hSC : S ≤ C := by
      rintro _ ⟨y, hy, rfl⟩
      exact hαC y (hQC hy)
    have hSn : ∀ g ∈ C, ∀ x ∈ S, g * x * g⁻¹ ∈ S := by
      rintro g hg _ ⟨y, hy, rfl⟩
      refine ⟨(α⁻¹ * g * α) * y * (α⁻¹ * g * α)⁻¹, ?_, ?_⟩
      · refine GLAPPrimeCoreOf_conj_mem _ ?_ y hy
        have e : α⁻¹ * g * α = α * g * α⁻¹ := by simp only [hαi]
        rw [e]
        exact hαC g hg
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    have hScop : Nat.Coprime p (Nat.card S) := by
      rw [hS, Subgroup.card_map_of_injective (MulAut.conj α).injective]
      exact hcop
    intro q hq
    exact le_GLAPPrimeCoreOf_of_normal hSC hSn hScop (Subgroup.mem_map.2 ⟨q, hq, rfl⟩)
  have hfix : ∀ q ∈ Q, α * q * α⁻¹ = q → q = 1 := by
    set L' := Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({s} : Set G) with hL'
    set N : Subgroup G := Q ⊓ Subgroup.centralizer ({α} : Set G) with hN
    have hNL : N ≤ L' := fun x hx => ⟨hx.2, hQC hx.1⟩
    have hNn : ∀ g ∈ L', ∀ x ∈ N, g * x * g⁻¹ ∈ N := by
      intro g hg x hx
      refine ⟨GLAPPrimeCoreOf_conj_mem g (hg.2) x hx.1, ?_⟩
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 hg.1
      have h2 := Subgroup.mem_centralizer_singleton_iff.1 hx.2
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      calc g * x * g⁻¹ * α = g * x * (g⁻¹ * α) := by group
        _ = g * x * (α * g⁻¹) := by
          rw [(Commute.inv_left (show Commute g α from h1)).eq]
        _ = g * (x * α) * g⁻¹ := by group
        _ = g * (α * x) * g⁻¹ := by rw [h2]
        _ = (g * α) * x * g⁻¹ := by group
        _ = α * (g * x * g⁻¹) := by rw [h1]; group
    have hNcop : Nat.Coprime p (Nat.card N) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcop
    have hle : N ≤ GLAPPrimeCoreOf p L' := le_GLAPPrimeCoreOf_of_normal hNL hNn hNcop
    rw [hL', hL] at hle
    intro q hq hqα
    have hqN : q ∈ N := ⟨hq, by
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      calc q * α = (α * q * α⁻¹) * α := by rw [hqα]
        _ = α * q := by group⟩
    exact Subgroup.mem_bot.1 (hle hqN)
  have hinvQ := inv_of_fixedPointFree_involution hα hQα hfix
  by_contra hne
  obtain ⟨⟨u, huQ⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hus : Commute s u :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hQC huQ)).symm
  have hcopu : Nat.Coprime p (orderOf u) :=
    Nat.Coprime.coprime_dvd_right (by
      have := orderOf_dvd_natCard (⟨u, huQ⟩ : Q)
      rwa [Subgroup.orderOf_mk] at this) hcop
  have hupos : 0 < orderOf u := orderOf_pos_iff.2 (isOfFinOrder_of_finite u)
  have hu1o : orderOf u ≠ 1 := fun h => hu1' (orderOf_eq_one_iff.1 h)
  have huodd : Odd (orderOf u) := by
    by_contra hev
    have h2 : 2 ∣ orderOf u := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hev)
    have hv := orderOf_pow_orderOf_div hupos.ne' h2
    set v : G := u ^ (orderOf u / 2) with hv'
    have hvQ : v ∈ Q := Q.pow_mem huQ _
    have hv2 : v⁻¹ = v := by
      have h2v : v ^ 2 = 1 := by rw [← hv]; exact pow_orderOf_eq_one v
      exact inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h2v)
    have := hfix v hvQ (by rw [hinvQ v hvQ, hv2])
    rw [this, orderOf_one] at hv
    omega
  have hap : orderOf (s * u) = p * orderOf u := by
    rw [hus.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hs]; exact hcopu), hs]
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have haodd : Odd (orderOf (s * u)) := by rw [hap]; exact hpodd.mul huodd
  have hainv : α * (s * u) * α⁻¹ = (s * u)⁻¹ := by
    calc α * (s * u) * α⁻¹ = (α * s * α⁻¹) * (α * u * α⁻¹) := by group
      _ = s⁻¹ * u⁻¹ := by rw [hinv, hinvQ u huQ]
      _ = (s * u)⁻¹ := by rw [mul_inv_rev, hus.symm.inv_inv.eq]
  have hconj := isConj_mul_of_inverts_odd hainv haodd
  have hb := hbd α _ (IsConj.refl α) hconj
  have hprod : α * ((s * u) * α) = (s * u)⁻¹ := by
    calc α * ((s * u) * α) = α * (s * u) * α⁻¹ := by rw [hαi]; group
      _ = (s * u)⁻¹ := hainv
  rw [hprod, orderOf_inv, hap] at hb
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hu3 : 3 ≤ orderOf u := by
    obtain ⟨k, hk⟩ := huodd
    omega
  nlinarith

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
