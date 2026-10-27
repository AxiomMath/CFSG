module

public import CFSG.GH74.GLS.Stage4.Q3n.Omega
public import CFSG.Dihedral.PerfectDihedralFourgroupAction

public section

namespace CFSG.GH74.GLS.Stage4.Q3n

open Subgroup

namespace Q3nSetting

variable {G : Type} [Group G] [Finite G] {n : ℕ} (S : Q3nSetting G n)

theorem w₀_mul_self : S.w₀ * S.w₀ = 1 := by
  have h : S.w₀ ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [S.w₀_ord])
  rwa [pow_two] at h

theorem w₀_mul_mul {h : G} (hh : h ∈ S.H) : S.w₀ * h * S.w₀ = h⁻¹ := by
  have := S.w₀_inv h hh
  rwa [inv_eq_of_mul_eq_one_right S.w₀_mul_self] at this

theorem w₀_mul_of_mem_Q {q : G} (hq : q ∈ S.Q) : S.w₀ * q = q⁻¹ * S.w₀ := by
  have h := S.w₀_mul_mul (S.Q_le_H hq)
  calc S.w₀ * q = S.w₀ * q * S.w₀ * S.w₀ := by
        rw [mul_assoc (S.w₀ * q), S.w₀_mul_self, mul_one]
    _ = q⁻¹ * S.w₀ := by rw [h]

@[expose] def complementR : Subgroup G where
  carrier := {x | x ∈ S.Q ∨ ∃ q ∈ S.Q, x = q * S.w₀}
  one_mem' := Or.inl S.Q.one_mem
  mul_mem' := by
    rintro a b (ha | ⟨p, hp, rfl⟩) (hb | ⟨q, hq, rfl⟩)
    · exact Or.inl (S.Q.mul_mem ha hb)
    · exact Or.inr ⟨a * q, S.Q.mul_mem ha hq, by rw [mul_assoc]⟩
    · refine Or.inr ⟨p * b⁻¹, S.Q.mul_mem hp (S.Q.inv_mem hb), ?_⟩
      calc p * S.w₀ * b = p * (S.w₀ * b) := by rw [mul_assoc]
        _ = p * (b⁻¹ * S.w₀) := by rw [S.w₀_mul_of_mem_Q hb]
        _ = p * b⁻¹ * S.w₀ := by rw [mul_assoc]
    · refine Or.inl ?_
      have h : p * S.w₀ * (q * S.w₀) = p * q⁻¹ := by
        calc p * S.w₀ * (q * S.w₀) = p * (S.w₀ * q) * S.w₀ := by simp only [mul_assoc]
          _ = p * (q⁻¹ * S.w₀) * S.w₀ := by rw [S.w₀_mul_of_mem_Q hq]
          _ = p * q⁻¹ * (S.w₀ * S.w₀) := by simp only [mul_assoc]
          _ = p * q⁻¹ := by rw [S.w₀_mul_self, mul_one]
      rw [h]
      exact S.Q.mul_mem hp (S.Q.inv_mem hq)
  inv_mem' := by
    rintro x (hx | ⟨q, hq, rfl⟩)
    · exact Or.inl (S.Q.inv_mem hx)
    · refine Or.inr ⟨q, hq, ?_⟩
      calc (q * S.w₀)⁻¹ = S.w₀⁻¹ * q⁻¹ := mul_inv_rev _ _
        _ = S.w₀ * q⁻¹ := by rw [inv_eq_of_mul_eq_one_right S.w₀_mul_self]
        _ = q⁻¹⁻¹ * S.w₀ := S.w₀_mul_of_mem_Q (S.Q.inv_mem hq)
        _ = q * S.w₀ := by rw [inv_inv]

theorem exists_complement (hn : 3 ≤ n) :
    ∃ R : Subgroup G, R ≤ Subgroup.centralizer (S.U : Set G) ∧ S.U ⊓ R = ⊥ ∧
      ∀ c ∈ Subgroup.centralizer (S.U : Set G), ∃ u ∈ S.U, ∃ r ∈ R, c = u * r := by
  have hk2 : 2 ≤ S.k := by have := S.k_ge hn; omega
  refine ⟨S.complementR, ?_, ?_, ?_⟩
  · rintro x (hx | ⟨q, hq, rfl⟩)
    · exact S.H_le_centralizer (S.Q_le_H hx)
    · exact Subgroup.mul_mem _ (S.H_le_centralizer (S.Q_le_H hq)) S.w₀_mem_centralizer
  · rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxU, hxR⟩
    rcases hxR with hx | ⟨q, hq, hxq⟩
    · have hmem : x ∈ S.U ⊓ S.Q := ⟨hxU, hx⟩
      rwa [S.U_inf_Q, Subgroup.mem_bot] at hmem
    · exfalso
      apply S.w₀_not_mem_H hk2
      have hw : S.w₀ = q⁻¹ * x := by rw [hxq]; group
      rw [hw]
      exact S.H.mul_mem (S.H.inv_mem (S.Q_le_H hq)) (S.U_le_H hxU)
  · intro c hc
    obtain ⟨h, hh, hch⟩ := S.C0_eq c hc
    obtain ⟨u, hu, q, hq, rfl⟩ := S.exists_mul_of_mem_H h hh
    rcases hch with rfl | rfl
    · exact ⟨u, hu, q, Or.inl hq, rfl⟩
    · exact ⟨u, hu, q * S.w₀, Or.inr ⟨q, hq, rfl⟩, by rw [mul_assoc]⟩

theorem isKleinFour_U : IsKleinFour ↥S.U := by
  refine ⟨S.U_card, ?_⟩
  have hdvd : Monoid.exponent ↥S.U ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
      rw [pow_two]
      exact Subtype.ext (S.U_exp x x.2)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exfalso
    have hsub : Subsingleton ↥S.U := Monoid.exp_eq_one_iff.mp h1
    have h := Nat.card_unique (α := ↥S.U)
    rw [S.U_card] at h
    omega
  · exact h1

theorem normalizerMonoidHom_eq_one_iff {g : G} (hg : g ∈ Subgroup.normalizer (S.U : Set G)) :
    S.U.normalizerMonoidHom ⟨g, hg⟩ = 1 ↔ g ∈ Subgroup.centralizer (S.U : Set G) := by
  rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]

theorem exists_aut_sq_ne_one :
    ∃ α ∈ S.U.normalizerMonoidHom.range, α ^ 2 ≠ 1 := by
  have haN : S.a ∈ Subgroup.normalizer (S.U : Set G) := S.W_norm_U S.a S.a_mem
  refine ⟨S.U.normalizerMonoidHom ⟨S.a, haN⟩, ⟨⟨S.a, haN⟩, rfl⟩, ?_⟩
  intro h2
  have ha3 : S.a ^ 3 = 1 := by
    have := pow_orderOf_eq_one S.a
    rwa [S.a_ord] at this
  have h3 : S.U.normalizerMonoidHom ⟨S.a, haN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨S.a, haN⟩ : Subgroup.normalizer (S.U : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using ha3)
    rw [this, map_one]
  have h1 : S.U.normalizerMonoidHom ⟨S.a, haN⟩ = 1 := by
    calc S.U.normalizerMonoidHom ⟨S.a, haN⟩
        = S.U.normalizerMonoidHom ⟨S.a, haN⟩ ^ 3 * (S.U.normalizerMonoidHom ⟨S.a, haN⟩ ^ 2)⁻¹ := by
          group
      _ = 1 := by rw [h3, h2]; simp
  have hC := (S.normalizerMonoidHom_eq_one_iff haN).1 h1
  obtain ⟨h0, hh0, hc⟩ := S.C0_eq S.a hC
  rcases hc with hc | hc
  · have haH : S.a ∈ S.H := hc ▸ hh0
    have h1' := S.nonsing S.a haH (by group)
    have h4 := S.a_ord
    rw [h1', orderOf_one] at h4
    omega
  · have hsq : S.a * S.a = 1 := by
      rw [hc]
      calc h0 * S.w₀ * (h0 * S.w₀) = h0 * (S.w₀ * h0 * S.w₀) := by simp only [mul_assoc]
        _ = 1 := by rw [S.w₀_mul_mul hh0]; group
    have hd : orderOf S.a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    rw [S.a_ord] at hd
    omega

theorem exists_aut_involution (hn : 3 ≤ n) :
    ∃ β ∈ S.U.normalizerMonoidHom.range, β ≠ 1 ∧ β ^ 2 = 1 := by
  have hk13 := S.k_ge hn
  obtain ⟨e⟩ := S.W_iso
  let w₀' : ↥S.W := ⟨S.w₀, S.w₀_mem_W⟩
  have hw₀ : e w₀' = DihedralGroup.r 3 := by
    apply d12_central_order_two
    · intro g
      obtain ⟨h, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (S.w₀_central h h.2)
    · intro h1
      have h3 : w₀' = 1 := e.injective (by rw [h1, map_one])
      have h2 : orderOf S.w₀ = 2 := S.w₀_ord
      have h4 : S.w₀ = 1 := congrArg Subtype.val h3
      rw [h4, orderOf_one] at h2
      omega
  obtain ⟨r, hr⟩ : ∃ r : ↥S.W, e r = DihedralGroup.sr 0 := ⟨e.symm _, e.apply_symm_apply _⟩
  have hr_ord : orderOf (r : G) = 2 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq e r, hr]
    exact DihedralGroup.orderOf_sr 0
  have hr_ne : (r : G) ≠ S.w₀ := by
    intro h
    have h' : r = w₀' := Subtype.ext h
    have h5 : DihedralGroup.sr (0 : ZMod 6) = DihedralGroup.r 3 := by rw [← hr, h', hw₀]
    simp at h5
  have hr2 : (r : G) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (r : G)
    rwa [hr_ord] at this
  have hrN : (r : G) ∈ Subgroup.normalizer (S.U : Set G) := S.W_norm_U r r.2
  refine ⟨S.U.normalizerMonoidHom ⟨(r : G), hrN⟩, ⟨_, rfl⟩, ?_, ?_⟩
  · intro h
    have hC := (S.normalizerMonoidHom_eq_one_iff hrN).1 h
    obtain ⟨h0, hh0, hc⟩ := S.C0_eq (r : G) hC
    have hfix := S.inv_fix (r : G) r.2 hr_ord hr_ne
    rcases hc with hc | hc
    · have hrH : (r : G) ∈ S.H := hc ▸ hh0
      have hall : ∀ q : ↥S.Q, (r : G) * (q : G) * (r : G)⁻¹ = (q : G) := by
        intro q
        rw [S.H_comm _ hrH _ (S.Q_le_H q.2)]
        group
      have hcard := Nat.card_congr (Equiv.subtypeUnivEquiv hall)
      rw [hfix, S.Q_card] at hcard
      nlinarith
    · have hrq : ∀ q : ↥S.Q, (r : G) * (q : G) * (r : G)⁻¹ = (q : G)⁻¹ := by
        intro q
        have h1 : S.w₀ * (q : G) * S.w₀⁻¹ = (q : G)⁻¹ := S.w₀_inv q (S.Q_le_H q.2)
        have h2 : h0 * (q : G)⁻¹ = (q : G)⁻¹ * h0 :=
          S.H_comm h0 hh0 _ (S.H.inv_mem (S.Q_le_H q.2))
        rw [hc]
        calc h0 * S.w₀ * (q : G) * (h0 * S.w₀)⁻¹ = h0 * (S.w₀ * (q : G) * S.w₀⁻¹) * h0⁻¹ := by group
          _ = h0 * (q : G)⁻¹ * h0⁻¹ := by rw [h1]
          _ = (q : G)⁻¹ := by rw [h2]; group
      have key : ∀ q : {q : ↥S.Q // (r : G) * (q : G) * (r : G)⁻¹ = (q : G)}, (q.1 : G) = 1 := by
        rintro ⟨q, hq⟩
        have hqq : (q : G)⁻¹ = q := (hrq q).symm.trans hq
        have hsq : (q : G) * q = 1 := by
          calc (q : G) * q = q * (q : G)⁻¹ := by rw [hqq]
            _ = 1 := mul_inv_cancel _
        exact S.eq_one_of_odd_sq q.2 hsq
      have hsub : Subsingleton {q : ↥S.Q // (r : G) * (q : G) * (r : G)⁻¹ = (q : G)} :=
        ⟨fun a b => Subtype.ext (Subtype.ext ((key a).trans (key b).symm))⟩
      have hle := Finite.card_le_one_iff_subsingleton.2 hsub
      rw [hfix] at hle
      omega
  · rw [← map_pow]
    have : (⟨(r : G), hrN⟩ : Subgroup.normalizer (S.U : Set G)) ^ 2 = 1 :=
      Subtype.ext (by simpa using hr2)
    rw [this, map_one]

theorem U_aut (hn : 3 ≤ n) : Function.Surjective S.U.normalizerMonoidHom := by
  have : IsKleinFour ↥S.U := S.isKleinFour_U
  obtain ⟨α, hα, hα2⟩ := S.exists_aut_sq_ne_one
  obtain ⟨β, hβ, hβ1, hβ2⟩ := S.exists_aut_involution hn
  exact MonoidHom.range_eq_top.mp
    (CFSG.GorensteinWalter.kleinFourAut_subgroup_eq_top ↥S.U _ α β hα hα2 hβ hβ1 hβ2)

end Q3nSetting

end CFSG.GH74.GLS.Stage4.Q3n
