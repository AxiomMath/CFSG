module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Prod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP15
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL414b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

private lemma k18k_zpowers_decomp {G : Type} [Group G] {Y : Subgroup G} {g : G}
    (hg2 : g ^ 2 ∈ Y) (n : ℤ) :
    (∃ z ∈ Y, g ^ n = z) ∨ (∃ z ∈ Y, g ^ n = z * g) := by
  have hdecomp : g ^ n = (g ^ (2 : ℤ)) ^ (n / 2) * g ^ (n % 2) := by
    have h : n = 2 * (n / 2) + n % 2 := (Int.mul_ediv_add_emod n 2).symm
    conv_lhs => rw [h]
    rw [zpow_add, zpow_mul]
  have hg2' : g ^ (2 : ℤ) ∈ Y := by simpa using hg2
  have hz : (g ^ (2 : ℤ)) ^ (n / 2) ∈ Y := Subgroup.zpow_mem Y hg2' (n / 2)
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left
    exact ⟨(g ^ (2 : ℤ)) ^ (n / 2), hz, by rw [hdecomp, h, zpow_zero, mul_one]⟩
  · right
    exact ⟨(g ^ (2 : ℤ)) ^ (n / 2), hz, by rw [hdecomp, h, zpow_one]⟩

private lemma k18k_zpowers_of_sq_one {G : Type} [Group G] {a : G} (ha : a ^ 2 = 1) {x : G}
    (hx : x ∈ zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases k18k_zpowers_decomp (Y := ⊥) (by simpa using ha) n with
    ⟨z, hz, hz_eq⟩ | ⟨z, hz, hz_eq⟩
  · left
    rw [hz_eq]
    simpa using (Subgroup.mem_bot.mp hz)
  · right
    rw [hz_eq]
    simp [Subgroup.mem_bot.mp hz]

private lemma k18k_card_sup_zpowers_le_of_comm {G : Type} [Group G] [Finite G]
    {Y : Subgroup G} {g : G} (hg2 : g ^ 2 ∈ Y) (hcomm : ∀ h ∈ Y, g * h = h * g) :
    Nat.card ↥(Y ⊔ zpowers g) ≤ 2 * Nat.card Y := by
  have hnorm : ∀ k ∈ zpowers g, ∀ h ∈ Y, k * h * k⁻¹ ∈ Y := by
    intro k hk h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    have hc0 : Commute g h := hcomm h hh
    have hc : Commute (g ^ n) h := hc0.zpow_left n
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
    exact hh
  have hle : Nat.card ↥(Y ⊔ zpowers g) ≤ Nat.card (↥Y × Fin 2) :=
    Nat.card_le_card_of_surjective
      (fun p : ↥Y × Fin 2 =>
        (⟨(p.1 : G) * g ^ (((p.2 : ℕ) : ℤ)),
          Subgroup.mul_mem_sup p.1.2
            (Subgroup.zpow_mem (zpowers g) (Subgroup.mem_zpowers g) _)⟩ : ↥(Y ⊔ zpowers g)))
      (by
        rintro ⟨x, hx⟩
        obtain ⟨y, hy, k, hk, rfl⟩ := (mem_sup_iff_of_normalizes hnorm).mp hx
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
        rcases k18k_zpowers_decomp hg2 m with ⟨z, hz, hz_eq⟩ | ⟨z, hz, hz_eq⟩
        · refine ⟨(⟨y * z, Y.mul_mem hy hz⟩, 0), ?_⟩
          apply Subtype.ext
          simp only [Fin.val_zero, Nat.cast_zero, zpow_zero, mul_one]
          rw [hz_eq]
        · refine ⟨(⟨y * z, Y.mul_mem hy hz⟩, 1), ?_⟩
          apply Subtype.ext
          simp only [Fin.val_one, Nat.cast_one, zpow_one]
          rw [hz_eq]
          group)
  rw [Nat.card_prod, Nat.card_fin] at hle
  calc Nat.card ↥(Y ⊔ zpowers g) ≤ Nat.card Y * 2 := hle
    _ = 2 * Nat.card Y := Nat.mul_comm _ _

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

@[expose] def k18B0 (t tau x₁ x₂ rho : G) : Subgroup G :=
  ctxYq t tau x₁ x₂ rho ⊔ closure {x₁ * x₂, tau}

theorem k18_card_Y_sup (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(ctxYq t tau x₁ x₂ rho ⊔ zpowers (x₁ * x₂)) = 2 ^ 5 := by
  set g : G := x₁ * x₂ with hgdef
  set Y : Subgroup G := ctxYq t tau x₁ x₂ rho with hYdef
  set Q : Subgroup G := ctxQ t tau x₁ x₂ rho with hQdef
  have hYQ : Y ≤ Q := ctxYq_le_ctxQ
  have hgQ : g ∈ Q := by
    rw [hgdef, hQdef]
    exact hc.base_le_Q (Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)))
  have hg2Y : g ^ 2 ∈ Y := by
    rw [hYdef]
    exact l17_V_le_Y hc (l17_Q_sq_mem hc g hgQ)
  have hYcard : Nat.card Y = 16 := by
    rw [hYdef]
    exact card_ctxYq hc.q_iso
  have hcomm : ∀ h ∈ Y, g * h = h * g := by
    intro h hh
    exact IsZ4Z4E4.comm hc.q_iso hgQ (hYQ hh)
  have hle : Nat.card ↥(Y ⊔ zpowers g) ≤ 32 := by
    have h := k18k_card_sup_zpowers_le_of_comm hg2Y hcomm
    rw [hYcard] at h
    norm_num at h
    exact h
  have hg_notY : g ∉ Y := by
    change g ∉ ctxYq t tau x₁ x₂ rho
    intro hgY
    have h2 : g ^ 2 = 1 := ((mem_ctxYq_iff hc.q_iso g).mp hgY).2
    apply (l17_yz_ne hc).2.1
    rw [← hgdef]
    exact h2
  have hgH : g ∈ Y ⊔ zpowers g := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have hne : Y ≠ Y ⊔ zpowers g := by
    intro heq
    exact hg_notY (by rwa [← heq] at hgH)
  have hdvd : Nat.card Y ∣ Nat.card ↥(Y ⊔ zpowers g) := Subgroup.card_dvd_of_le le_sup_left
  rw [hYcard] at hdvd
  obtain ⟨m, hm⟩ := hdvd
  have hmpos : 0 < m := by
    by_contra h
    have h0 : m = 0 := Nat.eq_zero_of_not_pos h
    rw [h0, mul_zero] at hm
    haveI : Nonempty ↥(Y ⊔ zpowers g) := ⟨⟨1, Subgroup.one_mem _⟩⟩
    have hpos : 0 < Nat.card ↥(Y ⊔ zpowers g) := Nat.card_pos
    rw [hm] at hpos
    exact Nat.lt_irrefl 0 hpos
  have hmne1 : m ≠ 1 := by
    intro h1
    rw [h1, mul_one, ← hYcard] at hm
    exact hne (Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq hm))
  have hmle : m ≤ 2 := by
    have : 16 * m ≤ 32 := by rw [← hm]; exact hle
    omega
  have hm2 : m = 2 := by omega
  rw [hm, hm2]
  norm_num

theorem k18_B0_card (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(k18B0 t tau x₁ x₂ rho) = 2 ^ 6 := by
  rw [k18B0]
  set g : G := x₁ * x₂ with hgdef
  set Y : Subgroup G := ctxYq t tau x₁ x₂ rho with hYdef
  set Q : Subgroup G := ctxQ t tau x₁ x₂ rho with hQdef
  have hYQ : Y ≤ Q := ctxYq_le_ctxQ
  have hgQ : g ∈ Q := by
    rw [hgdef, hQdef]
    exact hc.base_le_Q (Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)))
  have hcardYsup : Nat.card ↥(Y ⊔ zpowers g) = 2 ^ 5 := by
    rw [hYdef, hgdef]
    exact k18_card_Y_sup hc
  have htau2 : tau ^ 2 = 1 := (ctx13_relations hc).2.2.2.1
  have htau_ne : tau ≠ 1 := by
    intro h
    exact (ctx13_relations hc).2.2.2.2.1 (by rw [h]; exact Subgroup.one_mem (zpowers t))
  have htaucard : Nat.card (zpowers tau) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime htau2 htau_ne]
  have htau_norm_Y : ∀ y ∈ Y, tau * y * tau⁻¹ ∈ Y := by
    intro y hy
    have hyQ : y ∈ Q := hYQ hy
    have h2 : y ^ 2 = 1 :=
      ((mem_ctxYq_iff hc.q_iso y).mp (show y ∈ ctxYq t tau x₁ x₂ rho from hy)).2
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rwa [pow_two] at h2)
    rw [hc.tau_inv_Q y hyQ, hyinv]
    exact hy
  have htau_norm_H : ∀ x ∈ Y ⊔ zpowers g, tau * x * tau⁻¹ ∈ Y ⊔ zpowers g := by
    have hHT : Y ≤ (Y ⊔ zpowers g).comap (MulAut.conj tau).toMonoidHom := by
      intro y hy
      rw [Subgroup.mem_comap]
      change tau * y * tau⁻¹ ∈ Y ⊔ zpowers g
      exact Subgroup.mem_sup_left (htau_norm_Y y hy)
    have hKT : zpowers g ≤ (Y ⊔ zpowers g).comap (MulAut.conj tau).toMonoidHom := by
      intro k hk
      rw [Subgroup.mem_comap]
      change tau * k * tau⁻¹ ∈ Y ⊔ zpowers g
      have htau_g : tau * g * tau⁻¹ = g⁻¹ := hc.tau_inv_Q g hgQ
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      rw [show tau * g ^ n * tau⁻¹ = (tau * g * tau⁻¹) ^ n by
        rw [← MulAut.conj_apply tau (g ^ n), map_zpow (MulAut.conj tau) g n,
          MulAut.conj_apply tau g]]
      rw [htau_g, inv_zpow']
      exact Subgroup.mem_sup_right
        (Subgroup.zpow_mem (zpowers g) (Subgroup.mem_zpowers g) (-n))
    intro x hx
    exact Subgroup.mem_comap.mp (sup_le hHT hKT hx)
  have hKnorm : ∀ k ∈ zpowers tau, ∀ h ∈ Y ⊔ zpowers g, k * h * k⁻¹ ∈ Y ⊔ zpowers g := by
    intro k hk h hh
    rcases k18k_zpowers_of_sq_one htau2 hk with hk1 | hktau
    · rw [hk1, one_mul, inv_one, mul_one]; exact hh
    · rw [hktau]; exact htau_norm_H h hh
  have hHleQ : Y ⊔ zpowers g ≤ Q := sup_le hYQ (Subgroup.zpowers_le_of_mem hgQ)
  have htau_notQ : tau ∉ Q := Ctx13.tau_not_mem_Q hc
  have hbotQ : zpowers tau ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxt, hxQ⟩ := Subgroup.mem_inf.mp hx
    rcases k18k_zpowers_of_sq_one htau2 hxt with h | h
    · rw [h]; exact Subgroup.mem_bot.mpr rfl
    · rw [h] at hxQ; exact absurd hxQ htau_notQ
  have hHK : (Y ⊔ zpowers g) ⊓ zpowers tau = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxH, hxt⟩ := Subgroup.mem_inf.mp hx
    have hxQ : x ∈ Q := hHleQ hxH
    have : x ∈ zpowers tau ⊓ Q := ⟨hxt, hxQ⟩
    rwa [hbotQ] at this
  have hcl : closure ({g, tau} : Set G) = zpowers g ⊔ zpowers tau := by
    have hset : ({g, tau} : Set G) = ({g} : Set G) ∪ {tau} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    rw [hset, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure g,
      ← Subgroup.zpowers_eq_closure tau]
  have hB0 : Y ⊔ closure ({g, tau} : Set G) = (Y ⊔ zpowers g) ⊔ zpowers tau := by
    rw [hcl, sup_assoc]
  rw [hB0]
  rw [card_sup_eq_mul (H := Y ⊔ zpowers g) (K := zpowers tau) hKnorm hHK,
    hcardYsup, htaucard]
  norm_num

theorem k18_B0_cent (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    k18B0 t tau x₁ x₂ rho ⊓ centralizer ((k18B0 t tau x₁ x₂ rho : Subgroup G) : Set G) =
      ctxYq t tau x₁ x₂ rho := by
  rw [k18B0]
  set g : G := x₁ * x₂ with hgdef
  set Y : Subgroup G := ctxYq t tau x₁ x₂ rho with hYdef
  set Q : Subgroup G := ctxQ t tau x₁ x₂ rho with hQdef
  have hYQ : Y ≤ Q := ctxYq_le_ctxQ
  have hgQ : g ∈ Q := by
    rw [hgdef, hQdef]
    exact hc.base_le_Q (Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)))
  have htau2 : tau ^ 2 = 1 := (ctx13_relations hc).2.2.2.1
  have hHleQ : Y ⊔ zpowers g ≤ Q := sup_le hYQ (Subgroup.zpowers_le_of_mem hgQ)
  have htau_norm_Y : ∀ y ∈ Y, tau * y * tau⁻¹ ∈ Y := by
    intro y hy
    have hyQ : y ∈ Q := hYQ hy
    have h2 : y ^ 2 = 1 :=
      ((mem_ctxYq_iff hc.q_iso y).mp (show y ∈ ctxYq t tau x₁ x₂ rho from hy)).2
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rwa [pow_two] at h2)
    rw [hc.tau_inv_Q y hyQ, hyinv]
    exact hy
  have htau_norm_H : ∀ x ∈ Y ⊔ zpowers g, tau * x * tau⁻¹ ∈ Y ⊔ zpowers g := by
    have hHT : Y ≤ (Y ⊔ zpowers g).comap (MulAut.conj tau).toMonoidHom := by
      intro y hy
      rw [Subgroup.mem_comap]
      change tau * y * tau⁻¹ ∈ Y ⊔ zpowers g
      exact Subgroup.mem_sup_left (htau_norm_Y y hy)
    have hKT : zpowers g ≤ (Y ⊔ zpowers g).comap (MulAut.conj tau).toMonoidHom := by
      intro k hk
      rw [Subgroup.mem_comap]
      change tau * k * tau⁻¹ ∈ Y ⊔ zpowers g
      have htau_g : tau * g * tau⁻¹ = g⁻¹ := hc.tau_inv_Q g hgQ
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      rw [show tau * g ^ n * tau⁻¹ = (tau * g * tau⁻¹) ^ n by
        rw [← MulAut.conj_apply tau (g ^ n), map_zpow (MulAut.conj tau) g n,
          MulAut.conj_apply tau g]]
      rw [htau_g, inv_zpow']
      exact Subgroup.mem_sup_right
        (Subgroup.zpow_mem (zpowers g) (Subgroup.mem_zpowers g) (-n))
    intro x hx
    exact Subgroup.mem_comap.mp (sup_le hHT hKT hx)
  have hKnorm : ∀ k ∈ zpowers tau, ∀ h ∈ Y ⊔ zpowers g, k * h * k⁻¹ ∈ Y ⊔ zpowers g := by
    intro k hk h hh
    rcases k18k_zpowers_of_sq_one htau2 hk with hk1 | hktau
    · rw [hk1, one_mul, inv_one, mul_one]; exact hh
    · rw [hktau]; exact htau_norm_H h hh
  have hcl : closure ({g, tau} : Set G) = zpowers g ⊔ zpowers tau := by
    have hset : ({g, tau} : Set G) = ({g} : Set G) ∪ {tau} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    rw [hset, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure g,
      ← Subgroup.zpowers_eq_closure tau]
  have hB0 : Y ⊔ closure ({g, tau} : Set G) = (Y ⊔ zpowers g) ⊔ zpowers tau := by
    rw [hcl, sup_assoc]
  rw [hB0]
  have hgB0 : g ∈ (Y ⊔ zpowers g) ⊔ zpowers tau :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
  have htauB0 : tau ∈ (Y ⊔ zpowers g) ⊔ zpowers tau :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers tau)
  apply le_antisymm
  · intro b hb
    obtain ⟨hbB0, hbcent⟩ := Subgroup.mem_inf.mp hb
    obtain ⟨h, hh, k, hk, hbk⟩ := (mem_sup_iff_of_normalizes hKnorm).mp hbB0
    rcases k18k_zpowers_of_sq_one htau2 hk with hk1 | hktau
    · have hb_eq : b = h := by rw [hbk, hk1, mul_one]
      have hbQ : b ∈ Q := by rw [hb_eq]; exact hHleQ hh
      have hcomm : tau * b = b * tau :=
        (Subgroup.mem_centralizer_iff.mp hbcent) tau htauB0
      have hbinv : b = b⁻¹ := by
        have h1 : b = tau * b * tau⁻¹ := by rw [hcomm]; group
        exact h1.trans (hc.tau_inv_Q b hbQ)
      have hb2 : b * b = 1 := mul_eq_one_iff_eq_inv.mpr hbinv
      change b ∈ ctxYq t tau x₁ x₂ rho
      exact (mem_ctxYq_iff hc.q_iso b).mpr ⟨hbQ, by rwa [pow_two]⟩
    · exfalso
      have hb_eq : b = h * tau := by rw [hbk, hktau]
      have hbg : b * g = g * b :=
        ((Subgroup.mem_centralizer_iff.mp hbcent) g hgB0).symm
      have hconj1 : b * g * b⁻¹ = g := by rw [hbg]; group
      have hconj2 : b * g * b⁻¹ = g⁻¹ := by
        rw [hb_eq]
        have hcomm_hg : Commute h g := IsZ4Z4E4.comm hc.q_iso (hHleQ hh) hgQ
        calc (h * tau) * g * (h * tau)⁻¹
            = h * (tau * g * tau⁻¹) * h⁻¹ := by group
          _ = h * g⁻¹ * h⁻¹ := by rw [hc.tau_inv_Q g hgQ]
          _ = g⁻¹ := by
            rw [hcomm_hg.inv_right.eq, mul_assoc, mul_inv_cancel, mul_one]
      have hg_eq : g = g⁻¹ := hconj1.symm.trans hconj2
      have hg2 : g * g = 1 := mul_eq_one_iff_eq_inv.mpr hg_eq
      exact (l17_yz_ne hc).2.1 (by rw [← hgdef, pow_two]; exact hg2)
  · apply le_inf
    · exact le_sup_left.trans le_sup_left
    · rw [Subgroup.le_centralizer_iff]
      apply sup_le
      · apply sup_le
        · intro y hy
          rw [Subgroup.mem_centralizer_iff]
          intro y' hy'
          exact IsZ4Z4E4.comm hc.q_iso (hYQ hy') (hYQ hy)
        · intro k hk
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
          exact IsZ4Z4E4.comm hc.q_iso (hYQ hy) (Subgroup.zpow_mem Q hgQ n)
      · intro k hk
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
        have hc0 : Commute tau y := hc.tau_cent_Y y hy
        exact hc0.symm.zpow_right n

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
