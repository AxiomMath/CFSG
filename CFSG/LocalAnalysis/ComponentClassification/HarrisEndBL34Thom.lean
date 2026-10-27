module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34E4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndTransfer

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.LLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* PSL3Four.S}

theorem relIndex_W₀ (hL : LLayer hs π) {W : Subgroup X}
    (hWM : W ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
    (hW2 : IsPGroup 2 W) {a b : X} (haW : a ∈ W) (hbW : b ∈ W) (hab : a * b = b * a)
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (haS : ((hL.rho (QuotientGroup.mk ⟨a, hWM haW⟩) : PSL3Four.R) : Equiv.Perm (Fin 42)) ∉
      PSL3Four.S)
    (hbS : ((hL.rho (QuotientGroup.mk ⟨b, hWM hbW⟩) : PSL3Four.R) : Equiv.Perm (Fin 42)) ∉
      PSL3Four.S)
    (habS : ((hL.rho (QuotientGroup.mk ⟨a, hWM haW⟩ * QuotientGroup.mk ⟨b, hWM hbW⟩) :
      PSL3Four.R) : Equiv.Perm (Fin 42)) ∉ PSL3Four.S) :
    ((zpowers (hL.psi.comp (barHom hWM) ⟨a, haW⟩)).comap
        (hL.psi.comp (barHom hWM))).map W.subtype ≤ W ∧
      (((zpowers (hL.psi.comp (barHom hWM) ⟨a, haW⟩)).comap
        (hL.psi.comp (barHom hWM))).map W.subtype).relIndex W = 2 ∧
      b ∉ ((zpowers (hL.psi.comp (barHom hWM) ⟨a, haW⟩)).comap
        (hL.psi.comp (barHom hWM))).map W.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := hL.psi.comp (barHom hWM) with hφ
  set A := φ ⟨a, haW⟩ with hA
  set B := φ ⟨b, hbW⟩ with hB
  have hφa : A = hL.psi (QuotientGroup.mk ⟨a, hWM haW⟩) := rfl
  have hφb : B = hL.psi (QuotientGroup.mk ⟨b, hWM hbW⟩) := rfl
  have hψ1 : ∀ g, hL.psi g = 1 ↔ ((hL.rho g : PSL3Four.R) : Equiv.Perm (Fin 42)) ∈
      PSL3Four.S := fun g => by rw [← MonoidHom.mem_ker, hL.mem_ker_psi, hL.rho_mem_S_iff]
  have hA1 : A ≠ 1 := fun h => haS ((hψ1 _).mp (hφa ▸ h))
  have hB1 : B ≠ 1 := fun h => hbS ((hψ1 _).mp (hφb ▸ h))
  have hAB1 : A * B ≠ 1 := by
    intro h
    apply habS
    rw [← hψ1, map_mul, ← hφa, ← hφb]
    exact h
  have hA2 : A ^ 2 = 1 := by
    rw [hA, ← map_pow]
    have : (⟨a, haW⟩ : ↥W) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, ha2, Subgroup.coe_one])
    rw [this, map_one]
  have hB2 : B ^ 2 = 1 := by
    rw [hB, ← map_pow]
    have : (⟨b, hbW⟩ : ↥W) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hb2, Subgroup.coe_one])
    rw [this, map_one]
  have hABc : A * B = B * A := by
    rw [hA, hB, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hab
  have hrange4 : Nat.card φ.range = 4 := by
    have hle : Nat.card φ.range ≤ 4 := by
      have hdvd := Subgroup.card_subgroup_dvd_card φ.range
      rw [← Subgroup.index, index_SR] at hdvd
      have hp : IsPGroup 2 φ.range := hW2.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
      obtain ⟨k, hk⟩ := hp.exists_card_eq
      rw [hk] at hdvd ⊢
      have hk3 : k ≤ 2 := by
        by_contra hk3
        have : 2 ^ 3 ∣ 12 := (pow_dvd_pow 2 (by omega)).trans hdvd
        norm_num at this
      calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk3
        _ = 4 := by norm_num
    have hge : 4 ≤ Nat.card φ.range := by
      have hK : Nat.card ↥(zpowers A) = 2 := by
        rw [Nat.card_zpowers, orderOf_eq_prime hA2 hA1]
      have hn : ∀ k ∈ zpowers A, B * k * B⁻¹ ∈ zpowers A := by
        rintro _ ⟨n, rfl⟩
        have hBA : B * A * B⁻¹ = A := by rw [← hABc]; group
        change B * A ^ n * B⁻¹ ∈ zpowers A
        rw [← conj_zpow, hBA]
        exact zpow_mem (mem_zpowers A) n
      have hBK : B ∉ zpowers A := by
        intro h
        rcases EndB.eq_one_or_eq_of_mem_zpowers_sq hA2 h with h | h
        · exact hB1 h
        · apply hAB1
          rw [h, ← sq, hA2]
      have hcard := EndB.card_sup_zpowers hn (by rw [hB2]; exact one_mem _) hBK
      rw [hK] at hcard
      have hle' : zpowers A ⊔ zpowers B ≤ φ.range :=
        sup_le (zpowers_le.mpr ⟨_, rfl⟩) (zpowers_le.mpr ⟨_, rfl⟩)
      have := Subgroup.card_le_of_le hle'
      omega
    omega
  set W₀ := ((zpowers A).comap φ).map W.subtype with hW₀
  have hW₀W : W₀ ≤ W := map_subtype_le _
  have hsub : W₀.subgroupOf W = (zpowers A).comap φ := by
    rw [hW₀, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective (subtype_injective _)]
  refine ⟨hW₀W, ?_, ?_⟩
  · rw [Subgroup.relIndex, hsub, Subgroup.index_comap]
    have h1 := Subgroup.relIndex_mul_card (zpowers A) φ.range
    have hAr : zpowers A ≤ φ.range := zpowers_le.mpr ⟨_, rfl⟩
    rw [inf_of_le_left hAr, Nat.card_zpowers, orderOf_eq_prime hA2 hA1, hrange4] at h1
    omega
  · intro hb
    obtain ⟨w', hw', hw'b⟩ := hb
    have hw'eq : w' = ⟨b, hbW⟩ := Subtype.ext hw'b
    have hw'' : φ ⟨b, hbW⟩ ∈ zpowers A := by
      rw [← hw'eq]
      exact hw'
    rcases EndB.eq_one_or_eq_of_mem_zpowers_sq hA2 hw'' with h | h
    · exact hB1 (show B = 1 from h)
    · apply hAB1
      rw [show B = A from h, ← sq, hA2]

theorem two_dvd_index_W [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput) (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (hQc : IsCyclic ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W) :
    2 ∣ W.index := by
  by_contra hWX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxD, hx2, hxM, h0, h1⟩ := hL.exists_x hZ
  have hWM := hW.le
  have htM := hs.setup.t_mem_centralizer_beta i j
  have hTW : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ W := hs.beta.lt.le.trans hUW
  have htW : t ∈ W := hTW (mem_sup_left (mem_sup_left (mem_zpowers t)))
  have hxW : x ∈ W := hTW (mem_sup_left (mem_sup_right hxD))
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp
    (hs.standing.config.le_centralizer (mem_inf.mp hxD).2)
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have htb : hs.setup.tBar i j = (QuotientGroup.mk ⟨t, htM⟩ :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := rfl
  obtain ⟨-, hrtS⟩ := hL.rho_t_facts
  have hxbt := EndB.mk_comm hxM htM hxt
  obtain ⟨a, haW, ha2, hat, haS, hatS, d, hd, hda⟩ : ∃ a, ∃ haW : a ∈ W, a ^ 2 = 1 ∧
      a * t = t * a ∧
      ((hL.rho (QuotientGroup.mk ⟨a, hWM haW⟩) : PSL3Four.R) : Equiv.Perm (Fin 42)) ∉
        PSL3Four.S ∧
      ((hL.rho (QuotientGroup.mk ⟨a, hWM haW⟩ * QuotientGroup.mk ⟨t, hWM htW⟩) :
        PSL3Four.R) : Equiv.Perm (Fin 42)) ∉ PSL3Four.S ∧
      ∃ d ∈ PSL3Four.R, ((hL.rho (QuotientGroup.mk ⟨a, hWM haW⟩) : PSL3Four.R) :
        Equiv.Perm (Fin 42)) = d * PSL3Four.r₃ * d⁻¹ := by
    rcases hL.graph_unitary (EndB.mk_sq hxM hx2) hxbt h0 h1 with ⟨⟨d, hd, hdg⟩, -⟩ |
      ⟨-, ⟨d, hd, hdg⟩⟩
    · exact ⟨x, hxW, hx2, hxt, h0, h1, d, hd, hdg⟩
    · have hmk : (QuotientGroup.mk ⟨x * t, hWM (mul_mem hxW htW)⟩ :
          MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
          QuotientGroup.mk ⟨x, hxM⟩ * hs.setup.tBar i j := by
        rw [htb, ← QuotientGroup.mk_mul]
        rfl
      have htt : hs.setup.tBar i j * hs.setup.tBar i j = 1 := by rw [← sq]; exact hs.tBar_sq
      refine ⟨x * t, mul_mem hxW htW, ?_, ?_, ?_, ?_, d, hd, ?_⟩
      · rw [(show Commute x t from hxt).mul_pow, hx2, ht2, one_mul]
      · rw [← mul_assoc t x t, ← hxt]
      · rw [hmk]
        exact h1
      · rw [hmk]
        change ((hL.rho (QuotientGroup.mk ⟨x, hxM⟩ * hs.setup.tBar i j * hs.setup.tBar i j) :
          PSL3Four.R) : Equiv.Perm (Fin 42)) ∉ PSL3Four.S
        rw [mul_assoc (QuotientGroup.mk ⟨x, hxM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
          (hs.setup.tBar i j) (hs.setup.tBar i j), htt, mul_one]
        exact h0
      · rw [hmk]
        exact hdg
  obtain ⟨hW₀W, hidx, htW₀⟩ := hL.relIndex_W₀ hWM hW.isPGroup haW htW hat ha2 ht2 haS hrtS hatS
  obtain ⟨c, hcW₀, -, -⟩ := exists_extremal_conj_of_relIndex_two hnab hW.isPGroup hWX hW₀W hidx
    htW htW₀ ht2
  obtain ⟨w', hw', hw'eq⟩ := hcW₀
  have hτM : c⁻¹ * t * c⁻¹⁻¹ ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) := by
    rw [inv_inv, ← hw'eq]
    exact hWM w'.2
  set τb := (QuotientGroup.mk ⟨c⁻¹ * t * c⁻¹⁻¹, hτM⟩ :
    MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) with hτb
  have hφw : hL.psi.comp (barHom hWM) w' = hL.psi τb := by
    change hL.psi (QuotientGroup.mk ⟨_, hWM w'.2⟩) = hL.psi τb
    congr 2
    apply Subtype.ext
    change (w' : X) = c⁻¹ * t * c⁻¹⁻¹
    rw [inv_inv, ← hw'eq]
    rfl
  have hw'' : hL.psi.comp (barHom hWM) w' ∈ zpowers (hL.psi.comp (barHom hWM) ⟨a, haW⟩) := hw'
  rw [hφw] at hw''
  have hψ2 : (hL.psi.comp (barHom hWM) ⟨a, haW⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨a, haW⟩ : ↥W) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, ha2, Subgroup.coe_one])
    rw [this, map_one]
  have hτ2' : (c⁻¹ * t * c⁻¹⁻¹) ^ 2 = 1 := by
    rw [sq, show c⁻¹ * t * c⁻¹⁻¹ * (c⁻¹ * t * c⁻¹⁻¹) = c⁻¹ * (t * t) * c⁻¹⁻¹ by group, ← sq, ht2]
    group
  rcases EndB.eq_one_or_eq_of_mem_zpowers_sq hψ2 hw'' with h | h
  ·
    exact hL.false_of_conj_inner hZ hQc c⁻¹ hτM ((hL.mem_ker_psi τb).mp h)
  ·
    set ab := (QuotientGroup.mk ⟨a, hWM haW⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
      with habdef
    have h' : hL.psi (ab⁻¹ * τb) = 1 := by
      rw [map_mul, map_inv, h]
      exact inv_mul_cancel _
    have hS : ((hL.rho (ab⁻¹ * τb) : PSL3Four.R) : Equiv.Perm (Fin 42)) ∈ PSL3Four.S :=
      (hL.rho_mem_S_iff _).mpr ((hL.mem_ker_psi _).mp h')
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at hS
    have hra2 : ((hL.rho ab : PSL3Four.R) : Equiv.Perm (Fin 42)) * (hL.rho ab : PSL3Four.R) =
        1 := by
      rw [← Subgroup.coe_mul, ← map_mul, ← sq, habdef, EndB.mk_sq _ ha2, map_one,
        Subgroup.coe_one]
    have hrτ2 : ((hL.rho τb : PSL3Four.R) : Equiv.Perm (Fin 42)) * (hL.rho τb : PSL3Four.R) =
        1 := by
      rw [← Subgroup.coe_mul, ← map_mul, ← sq, hτb, EndB.mk_sq _ hτ2', map_one, Subgroup.coe_one]
    have hra1 : ((hL.rho ab : PSL3Four.R) : Equiv.Perm (Fin 42)) ≠ 1 :=
      fun h1 => haS (by rw [h1]; exact one_mem _)
    have hrτ1 : ((hL.rho τb : PSL3Four.R) : Equiv.Perm (Fin 42)) ≠ 1 := by
      intro h1
      rw [h1, mul_one] at hS
      exact haS (by simpa using inv_mem hS)
    obtain ⟨y, hyS, hy⟩ := CatFactsL4U4.conj_of_mul_mem_S (hL.rho ab).2 (hL.rho τb).2 hra2 hrτ2
      hra1 hrτ1 hS
    refine hL.false_of_graph_conj hFC hKC hI hKF hZ hτM ⟨y * d, mul_mem (PSL3Four.S_le_R hyS) hd,
      ?_⟩
    rw [← hτb, ← hy, hda]
    group

end EndB.LLayer

end CFSG.ComponentClassification.HarrisLit
