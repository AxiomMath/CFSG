module

public import CFSG.CGT.PushingUpLit.BlocksCommutePrime5
public import CFSG.CGT.PushingUpLit.BlocksCommutePrime4
public import CFSG.CGT.PushingUpLit.BlocksCommuteQuasi

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commute_of_odd_order {g q : G} {U : Subgroup G} (hU : ∀ u ∈ U, ∃ k : ℕ, u ^ 2 ^ k = 1)
    (hgU : ∀ u ∈ U, g * u * g⁻¹ = u) (hodd : Odd (orderOf g)) (hc : ⁅q, g⁆ ∈ U) :
    q * g = g * q := by
  obtain ⟨c, hcdef⟩ : ∃ c, c = ⁅q, g⁆ := ⟨_, rfl⟩
  have hcU : c ∈ U := hcdef ▸ hc
  have hgc : g * c * g⁻¹ = c := hgU c hcU
  have hcp : ∀ k : ℕ, g * (c ^ k)⁻¹ * g⁻¹ = (c ^ k)⁻¹ := by
    intro k
    have h1 : g * c ^ k * g⁻¹ = c ^ k := by
      rw [← conj_pow, hgc]
    calc g * (c ^ k)⁻¹ * g⁻¹ = (g * c ^ k * g⁻¹)⁻¹ := by group
      _ = (c ^ k)⁻¹ := by rw [h1]
  have hq : g * q * g⁻¹ = c⁻¹ * q := by
    rw [hcdef]
    simp only [commutatorElement_def]
    group
  have key : ∀ k : ℕ, g ^ k * q * (g ^ k)⁻¹ = (c ^ k)⁻¹ * q := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc g ^ (k + 1) * q * (g ^ (k + 1))⁻¹ = g * (g ^ k * q * (g ^ k)⁻¹) * g⁻¹ := by group
        _ = g * ((c ^ k)⁻¹ * q) * g⁻¹ := by rw [ih]
        _ = (g * (c ^ k)⁻¹ * g⁻¹) * (g * q * g⁻¹) := by group
        _ = (c ^ k)⁻¹ * (c⁻¹ * q) := by rw [hcp k, hq]
        _ = (c ^ (k + 1))⁻¹ * q := by group
  have h1 := key (orderOf g)
  rw [pow_orderOf_eq_one] at h1
  have h2 : (c ^ orderOf g)⁻¹ = 1 := by
    have : (c ^ orderOf g)⁻¹ * q = 1 * q := by simpa using h1.symm
    exact mul_right_cancel this
  have h3 : c ^ orderOf g = 1 := inv_eq_one.1 h2
  have h4 : c ∈ (⊥ : Subgroup G) :=
    mem_of_pow_mem_odd (hU c hcU) hodd ⊥ (by rw [h3]; exact one_mem _)
  have h5 : c = 1 := h4
  rw [h5] at hcdef
  exact commutatorElement_eq_one_iff_mul_comm.1 hcdef.symm

variable [Finite G]

theorem commutator_eq_bot_of_prime_normalizing {X Y : Subgroup G}
    (hG : IsCharacteristicP 2 G) (hX : IsBlockOf X) (hY : IsBlockOf Y) {p : ℕ}
    (hprime : p.Prime) (hXp : Nat.card (↥X ⧸ pCore 2 ↥X) = p)
    (hYp : Nat.card (↥Y ⧸ pCore 2 ↥Y) = p) (hXY : X ≤ Subgroup.normalizer (Y : Set G))
    (hYX : Y ≤ Subgroup.normalizer (X : Set G)) (hne : X ≠ Y) : ⁅X, Y⁆ = ⊥ := by
  obtain ⟨x, hx, hxo⟩ := exists_orderOf_eq_of_prime_top hprime hXp
  obtain ⟨y, hy, hyo⟩ := exists_orderOf_eq_of_prime_top hprime hYp
  have dX := isPrimeBlockData_of hX.2 hprime hXp hx hxo
  have dY := isPrimeBlockData_of hY.2 hprime hYp hy hyo
  have hxp : x ^ p = 1 := hxo ▸ pow_orderOf_eq_one x
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  have : Fact p.Prime := ⟨hprime⟩
  have hK : barImg X ⊓ barImg Y = ⊥ := by
    have hdvd : Nat.card ↥(barImg X ⊓ barImg Y) ∣ Nat.card ↥(barImg X) :=
      Subgroup.card_dvd_of_le inf_le_left
    rw [card_barImg hX, hXp] at hdvd
    rcases (Nat.dvd_prime hprime).1 hdvd with h1 | h1
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      have heq : barImg X ⊓ barImg Y = barImg X := by
        refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
        rw [h1, card_barImg hX, hXp]
      have hle : barImg X ≤ barImg Y := by
        rw [← heq]
        exact inf_le_right
      have e1 : X ≤ Y := le_of_le_sup_pCore hX hY (le_sup_pCore_of_barImg_le hle)
      exact hne (eq_of_le_of_isBlock hX hY e1)
  have hD : ∀ d ∈ X, d ∈ Y → d ∈ blockU X ∧ d ∈ blockU Y := by
    intro d hdX hdY
    have hmem : (QuotientGroup.mk' (pCore 2 G)) d ∈ barImg X ⊓ barImg Y :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem _ hdX, Subgroup.mem_map_of_mem _ hdY⟩
    rw [hK, Subgroup.mem_bot] at hmem
    have hQ : d ∈ pCore 2 G := (QuotientGroup.eq_one_iff d).1 hmem
    refine ⟨?_, ?_⟩
    · rw [← dX.oTwoIn_eq, oTwoIn_eq_inf_pCore hX.1]
      exact Subgroup.mem_inf.2 ⟨hdX, hQ⟩
    · rw [← dY.oTwoIn_eq, oTwoIn_eq_inf_pCore hY.1]
      exact Subgroup.mem_inf.2 ⟨hdY, hQ⟩
  have hE : ∀ a ∈ X, ∀ b ∈ Y, ⁅a, b⁆ ∈ blockU X ∧ ⁅a, b⁆ ∈ blockU Y := by
    intro a ha b hb
    refine hD _ ?_ ?_
    · have h1 : b * a⁻¹ * b⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 (hYX hb) a⁻¹).1 (inv_mem ha)
      have : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact mul_mem ha h1
    · have h1 : a * b * a⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.1 (hXY ha) b).1 hb
      have : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact mul_mem h1 (inv_mem hb)
  by_cases hI : blockU X ⊓ blockU Y = ⊥
  · refine le_bot_iff.1 (Subgroup.commutator_le.2 fun a ha b hb => ?_)
    have := hE a ha b hb
    rw [← Subgroup.mem_inf, hI] at this
    exact this
  exfalso
  have hIx : ∀ n ∈ blockU X ⊓ blockU Y, x * n * x⁻¹ ∈ blockU X ⊓ blockU Y := by
    intro n hn
    exact Subgroup.mem_inf.2 ⟨conj_mem_blockU (Subgroup.le_normalizer hx) hn.1,
      conj_mem_blockU (hXY hx) hn.2⟩
  have hIy : ∀ n ∈ blockU X ⊓ blockU Y, y * n * y⁻¹ ∈ blockU X ⊓ blockU Y := by
    intro n hn
    exact Subgroup.mem_inf.2 ⟨conj_mem_blockU (hYX hy) hn.1,
      conj_mem_blockU (Subgroup.le_normalizer hy) hn.2⟩
  have hUX : blockU X ⊓ blockU Y = blockU X := by
    rcases dX.irr _ inf_le_left hIx with h | h
    · exact absurd h hI
    · exact h
  have hUY : blockU X ⊓ blockU Y = blockU Y := by
    rcases dY.irr _ inf_le_right hIy with h | h
    · exact absurd h hI
    · exact h
  have hUW : blockU X = blockU Y := hUX.symm.trans hUY
  have hxN : x ∈ Subgroup.normalizer (blockU X : Set G) := le_normalizer_blockU X hx
  have hyN : y ∈ Subgroup.normalizer (blockU X : Set G) := by
    have := le_normalizer_blockU Y hy
    rwa [← hUW] at this
  have hUcomm : ∀ {u v : G}, u ∈ blockU X → v ∈ blockU X → u * v = v * u :=
    fun hu hv => blockU_commute hX.2 hu hv
  let _ : CommGroup ↥(blockU X) :=
    { (inferInstance : Group ↥(blockU X)) with
      mul_comm := fun a b => Subtype.ext (hUcomm a.2 b.2) }
  let σx : MulAut ↥(blockU X) := Subgroup.normalizerMonoidHom (blockU X) ⟨x, hxN⟩
  let σy : MulAut ↥(blockU X) := Subgroup.normalizerMonoidHom (blockU X) ⟨y, hyN⟩
  have hσxpow : ∀ (k : ℕ) (u : ↥(blockU X)),
      (((σx ^ k) u : ↥(blockU X)) : G) = x ^ k * u * (x ^ k)⁻¹ := by
    intro k u
    have h1 : σx ^ k = Subgroup.normalizerMonoidHom (blockU X) (⟨x, hxN⟩ ^ k) :=
      (map_pow _ _ _).symm
    rw [h1, Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  have hσypow : ∀ (k : ℕ) (u : ↥(blockU X)),
      (((σy ^ k) u : ↥(blockU X)) : G) = y ^ k * u * (y ^ k)⁻¹ := by
    intro k u
    have h1 : σy ^ k = Subgroup.normalizerMonoidHom (blockU X) (⟨y, hyN⟩ ^ k) :=
      (map_pow _ _ _).symm
    rw [h1, Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  have hσx1 : σx ^ p = 1 := by
    refine MulEquiv.ext fun u => Subtype.ext ?_
    rw [hσxpow, hxp]
    simp
  have hσy1 : σy ^ p = 1 := by
    refine MulEquiv.ext fun u => Subtype.ext ?_
    rw [hσypow, hyp]
    simp
  have hσxne : σx ≠ 1 := by
    intro h1
    have hcent : blockU X ≤ blockZ X := by
      intro u hu
      refine Subgroup.mem_inf.2 ⟨hu, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨r, hr, k, hk⟩ := dX.decomp g hg
      have hrU : r ∈ blockU X := dX.oTwoIn_eq ▸ hr
      have hxk : x ^ k * u * (x ^ k)⁻¹ = u := by
        have := hσxpow k ⟨u, hu⟩
        rw [h1, one_pow] at this
        exact this.symm
      have hc : r * u = u * r := hUcomm hrU hu
      rw [hk]
      calc r * x ^ k * u = r * (x ^ k * u * (x ^ k)⁻¹) * x ^ k := by group
        _ = r * u * x ^ k := by rw [hxk]
        _ = u * (r * x ^ k) := by rw [hc]; group
    rw [dX.blockZ_eq] at hcent
    exact blockU_ne_bot_of_short hX.2 (le_bot_iff.1 hcent)
  have hσxo : orderOf σx = p := orderOf_eq_prime hσx1 hσxne
  have hσcomm : σx * σy = σy * σx := by
    refine MulEquiv.ext fun u => Subtype.ext ?_
    have hc : ⁅x, y⁆ ∈ blockU X := (hE x hx y hy).1
    have hv : y * (x * (u : G) * x⁻¹) * y⁻¹ ∈ blockU X :=
      (Subgroup.mem_normalizer_iff.1 hyN _).1 ((Subgroup.mem_normalizer_iff.1 hxN _).1 u.2)
    have hcv : ⁅x, y⁆ * (y * (x * (u : G) * x⁻¹) * y⁻¹) =
        (y * (x * (u : G) * x⁻¹) * y⁻¹) * ⁅x, y⁆ := hUcomm hc hv
    have h1 := hσxpow 1 ((σy ^ 1) u)
    have h2 := hσypow 1 ((σx ^ 1) u)
    have e : x * (y * (u : G) * y⁻¹) * x⁻¹ =
        ⁅x, y⁆ * (y * (x * (u : G) * x⁻¹) * y⁻¹) * ⁅x, y⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    show (((σx (σy u)) : ↥(blockU X)) : G) = (((σy (σx u)) : ↥(blockU X)) : G)
    have h3 := hσxpow 1 (σy u)
    have h4 := hσypow 1 u
    have h5 := hσypow 1 (σx u)
    have h6 := hσxpow 1 u
    simp only [pow_one] at h3 h4 h5 h6
    rw [h3, h4, h5, h6, e, hcv]
    group
  have hirr : ∀ J : Subgroup ↥(blockU X), (∀ a ∈ J, σx a ∈ J) → J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    have hJ' : ∀ n ∈ J.map (blockU X).subtype, x * n * x⁻¹ ∈ J.map (blockU X).subtype := by
      rintro _ ⟨a, ha, rfl⟩
      refine ⟨σx a, hJ a ha, ?_⟩
      have := hσxpow 1 a
      simpa using this
    have hJU : J.map (blockU X).subtype ≤ blockU X := by
      rintro _ ⟨a, -, rfl⟩
      exact a.2
    rcases dX.irr _ hJU hJ' with h | h
    · left
      apply Subgroup.map_injective (blockU X).subtype_injective
      rw [h, Subgroup.map_bot]
    · right
      apply Subgroup.map_injective (blockU X).subtype_injective
      rw [h, Subgroup.map_top, Subgroup.range_subtype]
  have hnt : Nontrivial ↥(blockU X) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 (blockU_ne_bot_of_short hX.2)
  obtain ⟨m, hm⟩ := exists_pow_eq_of_irreducible hσxo hσy1 hσcomm hirr
  have hyx : ∀ u ∈ blockU X, y * u * y⁻¹ = x ^ m * u * (x ^ m)⁻¹ := by
    intro u hu
    have := congrArg (fun t : MulAut ↥(blockU X) => ((t ⟨u, hu⟩ : ↥(blockU X)) : G)) hm
    have h1 := hσypow 1 ⟨u, hu⟩
    rw [pow_one] at h1
    rw [hσxpow m ⟨u, hu⟩] at this
    rw [← this, h1]
    simp
  obtain ⟨g, hgdef⟩ : ∃ g, g = (x ^ m)⁻¹ * y := ⟨_, rfl⟩
  have hgU : ∀ u ∈ blockU X, g * u * g⁻¹ = u := by
    intro u hu
    have e : g * u * g⁻¹ = (x ^ m)⁻¹ * (y * u * y⁻¹) * x ^ m := by
      rw [hgdef]
      group
    rw [e, hyx u hu]
    group
  have hgk : ∀ k : ℕ, ∀ u ∈ blockU X, g ^ k * u * (g ^ k)⁻¹ = u := by
    intro k
    induction k with
    | zero => intro u hu; simp
    | succ k ih =>
      intro u hu
      calc g ^ (k + 1) * u * (g ^ (k + 1))⁻¹ = g ^ k * (g * u * g⁻¹) * (g ^ k)⁻¹ := by group
        _ = g ^ k * u * (g ^ k)⁻¹ := by rw [hgU u hu]
        _ = u := ih u hu
  let M : Subgroup G :=
    { carrier := {c | c ∈ Subgroup.normalizer (blockU X : Set G) ∧
        ∀ q ∈ pCore 2 G, ⁅q, c⁆ ∈ blockU X}
      one_mem' := ⟨one_mem _, fun q _ => by simp⟩
      mul_mem' := by
        rintro c c' ⟨hc, hc'⟩ ⟨hd, hd'⟩
        refine ⟨mul_mem hc hd, fun q hq => ?_⟩
        have e : ⁅q, c * c'⁆ = ⁅q, c⁆ * (c * ⁅q, c'⁆ * c⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem (hc' q hq) ((Subgroup.mem_normalizer_iff.1 hc _).1 (hd' q hq))
      inv_mem' := by
        rintro c ⟨hc, hc'⟩
        refine ⟨inv_mem hc, fun q hq => ?_⟩
        have e : ⁅q, c⁻¹⁆ = c⁻¹ * ⁅q, c⁆⁻¹ * c := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hc) _).1 (inv_mem (hc' q hq))
        simpa using this }
  have hXM : X ≤ M := fun a ha =>
    ⟨le_normalizer_blockU X ha, fun q hq => commutator_pCore_mem_blockU hX hq a ha⟩
  have hYM : Y ≤ M := fun b hb => by
    refine ⟨?_, fun q hq => ?_⟩
    · have := le_normalizer_blockU Y hb
      rwa [← hUW] at this
    · rw [hUW]
      exact commutator_pCore_mem_blockU hY hq b hb
  have hgM : g ∈ M := by
    rw [hgdef]
    exact mul_mem (inv_mem (hXM (pow_mem hx m))) (hYM hy)
  obtain ⟨a, m', hm'odd, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hgpo : orderOf (g ^ 2 ^ a) = m' := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m', hn⟩, hn,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
  have hgpC : g ^ 2 ^ a ∈ Subgroup.centralizer (pCore 2 G : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact commute_of_odd_order (U := blockU X)
      (fun u hu => exists_pow_eq_one_of_mem_oTwoIn (blockU_le_oTwoIn X hu))
      (hgk (2 ^ a)) (hgpo ▸ hm'odd) ((pow_mem hgM _).2 q hq)
  have hgpQ : g ^ 2 ^ a ∈ pCore 2 G := hG hgpC
  have hgQ : g ∈ pCore 2 G := by
    let π := QuotientGroup.mk' (pCore 2 G)
    have hπxy : π x * π y = π y * π x := by
      have hc : ⁅x, y⁆ ∈ pCore 2 G := blockU_le_pCore hX (hE x hx y hy).1
      have : π ⁅x, y⁆ = 1 := (QuotientGroup.eq_one_iff _).2 hc
      rw [map_commutatorElement] at this
      exact commutatorElement_eq_one_iff_mul_comm.1 this
    have hπx : π x ^ p = 1 := by rw [← map_pow, hxp, map_one]
    have hπy : π y ^ p = 1 := by rw [← map_pow, hyp, map_one]
    have h1 : (π g) ^ 2 ^ a = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).2 hgpQ
    have h2 : (π g) ^ p = 1 := by
      have hcom : Commute ((π x ^ m)⁻¹) (π y) :=
        ((show Commute (π x) (π y) from hπxy).pow_left m).inv_left
      rw [hgdef, map_mul, map_inv, map_pow, hcom.mul_pow, inv_pow, ← pow_mul, mul_comm,
        pow_mul, hπx, one_pow, inv_one, hπy, one_mul]
    have hcop : Nat.Coprime (2 ^ a) p :=
      Nat.Coprime.pow_left a ((Nat.coprime_primes Nat.prime_two hprime).2 (Ne.symm dX.odd))
    have h3 : orderOf (π g) ∣ Nat.gcd (2 ^ a) p :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact (QuotientGroup.eq_one_iff _).1 h3
  have hyXQ : y ∈ X ⊔ pCore 2 G := by
    have : y = x ^ m * g := by rw [hgdef]; group
    rw [this]
    exact Subgroup.mul_mem_sup (pow_mem hx m) hgQ
  have hYXQ : Y ≤ X ⊔ pCore 2 G := by
    intro b hb
    obtain ⟨r, hr, k, hk⟩ := dY.decomp b hb
    rw [hk]
    exact mul_mem (Subgroup.mem_sup_right (oTwoIn_le_pCore hY.1 hr)) (pow_mem hyXQ k)
  exact hne (eq_of_le_of_isBlock hY hX (le_of_le_sup_pCore hY hX hYXQ)).symm

end CFSG.CGT.PushingUpLit
