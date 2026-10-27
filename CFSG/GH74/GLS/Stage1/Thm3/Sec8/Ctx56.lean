module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx52

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}
  {Y : Subgroup G} {t w : G}

theorem invol_P_conj (hII : II4_4_4_center) (h31 : IVK_3_1a_lifted)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : ∀ x ∈ Pz S z, orderOf x = 2 → IsConj z x := by
  obtain ⟨u', hu'P, hu'c, hu'z⟩ := hs.fused.fused
  have hord' : orderOf u' = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hu'c
    rw [← hc, orderOf_conj', hs.fused.std.orderOf_z]
  exact (lemma_4_2 hII h31 G z S K₁ K₂ hs.fused.std
    ⟨u', Subgroup.mem_sup_left hu'P, hord', hu'c, hu'z⟩).1

theorem Nh_elems (cfg : Cfg88 z S K₁ W₂ U u h Y t w) :
    ∀ x ∈ Nh S h, x = 1 ∨ x = t ∨ x = w ∨ x = t * w := by
  intro x hx
  rw [cfg.hDeq] at hx
  have hc : ∀ a ∈ zpowers w, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hcom : Commute w t := cfg.htw.symm
    exact (hcom.zpow_zpow i j).eq
  obtain ⟨a, ha, b, hb, rfl⟩ := Basic.mem_sup_of_le_normalizer' (A := zpowers t) (B := zpowers w)
    (Basic.le_normalizer_of_commute' hc) hx
  rcases (Basic.mem_zpowers_of_sq' cfg.ht2).1 ha with h1 | h1 <;>
    rcases (Basic.mem_zpowers_of_sq' cfg.hw2).1 hb with h2 | h2
  · left; rw [h1, h2, one_mul]
  · right; right; left; rw [h1, h2, one_mul]
  · right; left; rw [h1, h2, mul_one]
  · right; right; right; rw [h1, h2]

theorem tw_sq (cfg : Cfg88 z S K₁ W₂ U u h Y t w) : (t * w) * (t * w) = 1 := by
  calc (t * w) * (t * w) = t * (w * t) * w := by group
    _ = t * (t * w) * w := by rw [← cfg.htw]
    _ = (t * t) * (w * w) := by group
    _ = 1 := by rw [cfg.ht2, cfg.hw2, one_mul]

theorem Nh_sq (cfg : Cfg88 z S K₁ W₂ U u h Y t w) : ∀ x ∈ Nh S h, x * x = 1 := by
  intro x hx
  rcases Nh_elems cfg x hx with h1 | h1 | h1 | h1
  · rw [h1, one_mul]
  · rw [h1]; exact cfg.ht2
  · rw [h1]; exact cfg.hw2
  · rw [h1]; exact tw_sq cfg

theorem S4_mem_U (cfg : Cfg88 z S K₁ W₂ U u h Y t w) (hsq : ∀ a ∈ Y, a * a ∈ U) :
    ∀ s ∈ S, s ^ 4 ∈ U := by
  intro s hs
  obtain ⟨y, hy, d', hd', rfl⟩ := cfg.hY.decomp s hs
  have hd'2 := Nh_sq cfg d' hd'
  have h1 : (y * d') * (y * d') = y * (d' * y * d'⁻¹) := by
    calc (y * d') * (y * d') = y * (d' * y * d'⁻¹) * (d' * d') := by group
      _ = y * (d' * y * d'⁻¹) := by rw [hd'2, mul_one]
  have hmem : (y * d') * (y * d') ∈ Y := by
    rw [h1]
    exact mul_mem hy (cfg.hY.norm_D d' hd' y hy)
  have h4 : (y * d') ^ 4 = ((y * d') * (y * d')) * ((y * d') * (y * d')) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [h4]
  exact hsq _ hmem

theorem Z_S_le (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (cfg : Cfg88 z S K₁ W₂ U u h Y t w) :
    ∀ c ∈ S, (∀ s ∈ S, s * c = c * s) → c = 1 ∨ c = z := by
  intro c hcS hcen
  have hcA : c ∈ Aof S K₁ W₂ h := by
    rw [← hs.cent_eq hII hq hrec]
    refine Subgroup.mem_inf.2 ⟨hcS, Subgroup.mem_centralizer_iff.2 (fun a ha => ?_)⟩
    exact hcen a (hs.A_le_S hII hq hrec ha)
  have hwS : w ∈ S := Nh_le_S cfg.hwD
  have htS : t ∈ S := Nh_le_S cfg.htD
  have hwc : w * c * w⁻¹ = c := by
    rw [hcen w hwS]
    group
  have hcc : c * c = 1 := by
    have h1 := cfg.hinvA c hcA
    rw [hwc] at h1
    calc c * c = c * c⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel c
  have hcU : c ∈ U := hs.A_inv_mem_U hII hq hrec hcA hcc
  have htc : t * c * t⁻¹ = c := by
    rw [hcen t htS]
    group
  have hzt : t * z * t⁻¹ = z := by rw [← hs.z_comm hII htS]; group
  have hzz := hs.z_sq
  rcases hs.U_elems c hcU with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso
    rw [h1, cfg.htu] at htc
    apply hs.z_ne
    have : u * z = u * 1 := by rw [mul_one]; exact htc
    exact mul_left_cancel this
  · exfalso
    rw [h1] at htc
    have h2 : t * (u * z) * t⁻¹ = u := by
      calc t * (u * z) * t⁻¹ = (t * u * t⁻¹) * (t * z * t⁻¹) := by group
        _ = (u * z) * z := by rw [cfg.htu, hzt]
        _ = u := by rw [mul_assoc, hzz, mul_one]
    rw [h2] at htc
    apply hs.z_ne
    have : u * 1 = u * z := by rw [mul_one]; exact htc
    exact (mul_left_cancel this).symm

theorem no_conj_in_C (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    {d : G} (hdS : d ∈ S) (hdP : d ∉ Pz S z) :
    ∀ b : G, b⁻¹ * d * b = u → b * z = z * b → False := by
  intro b hbd hbz
  have hM := hs.m4 hII
  have hbC : b ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hbz
  have huP : u ∈ Pz S z := hs.U_le_Pz hII hq hs.u_mem
  have huK : u ∈ K₁ ⊔ K₂ := by
    rw [Pz_eq hs.fused.std] at huP
    exact huP.2
  have hdK : d ∈ K₁ ⊔ K₂ := by
    have := hM.C_norm_K hbC huK
    have e : b * u * b⁻¹ = d := by rw [← hbd]; group
    rwa [e] at this
  apply hdP
  rw [Pz_eq hs.fused.std]
  exact ⟨hdS, hdK⟩

theorem exists_w₁ (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (hQ₁16 : Nat.card ↥(Qof S K₁) = 16) :
    ∃ w₁ ∈ S, w₁ * u = u * w₁ ∧ w₁ ^ 4 = z := by
  have hW₁8 : Nat.card ↥W₁ = 8 := by
    have := hs.card_W₁ hII
    omega
  obtain ⟨g, hg⟩ := hs.W₁_max.2.1.exists_generator
  have hgo : orderOf (g : G) = 8 := by
    have h1 : Nat.card ↥(zpowers g) = orderOf g := Nat.card_zpowers g
    have h2 : zpowers g = ⊤ := (Subgroup.eq_top_iff' _).2 hg
    rw [h2, Subgroup.card_top, hW₁8] at h1
    rw [Subgroup.orderOf_coe g]
    exact h1.symm
  have hgQ : (g : G) ∈ Qof S K₁ := hs.W₁_le_Q₁ g.2
  have hg4 : ((g : G) ^ 4) * ((g : G) ^ 4) = 1 := by
    have : (g : G) ^ 8 = 1 := by
      have := pow_orderOf_eq_one (g : G)
      rwa [hgo] at this
    calc ((g : G) ^ 4) * ((g : G) ^ 4) = (g : G) ^ 8 := by rw [← pow_add]
      _ = 1 := this
  have hg4Q : (g : G) ^ 4 ∈ Qof S K₁ := pow_mem hgQ 4
  have hg4z : (g : G) ^ 4 = z := by
    rcases (hs.gq_Q₁ hII).uniq _ hg4Q hg4 with h1 | h1
    · exfalso
      have := orderOf_dvd_of_pow_eq_one h1
      rw [hgo] at this
      omega
    · exact h1
  refine ⟨(g : G), hgQ.1, ?_, hg4z⟩
  obtain ⟨v₁, hv₁, v₂, hv₂, huv, -, -⟩ := hs.u_decomp hII hq
  have hv₁P : v₁ ∈ Pof S K₁ := hv₁.2
  have hv₂W : v₂ ∈ W₁ := hv₂.1
  have c1 : (g : G) * v₁ = v₁ * (g : G) := hs.Q_comm_P hII (K := K₁) (Or.inl rfl) _ hgQ v₁ hv₁P
  have c2 : (g : G) * v₂ = v₂ * (g : G) :=
    Basic.cyc_comm hs.W₁_max.2.1 _ g.2 v₂ hv₂W
  rw [huv]
  calc (g : G) * (v₁ * v₂) = (g * v₁) * v₂ := by group
    _ = (v₁ * g) * v₂ := by rw [c1]
    _ = v₁ * (g * v₂) := by group
    _ = v₁ * (v₂ * g) := by rw [c2]
    _ = (v₁ * v₂) * g := by group

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
