module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Fuse

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

theorem EndB.exists_mem_normalizer_of_ne {G : Type*} [Group G] [Finite G] {H P : Subgroup G}
    (hP : IsPGroup 2 P) (hHP : H ≤ P) (hne : H ≠ P) :
    ∃ y ∈ P, y ∈ normalizer (H : Set G) ∧ y ∉ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlt : H.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hne (le_antisymm hHP fun x hx => ?_)
    have : (⟨x, hx⟩ : P) ∈ H.subgroupOf P := h ▸ mem_top _
    exact this
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := P) _ hlt
  obtain ⟨y₀, hy₀N, hy₀H⟩ := IsConcreteLE.exists_of_lt hnc
  refine ⟨y₀, y₀.2, ?_, hy₀H⟩
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact (mem_normalizer_iff.mp hy₀N ⟨x, hHP hx⟩).mp (show (⟨x, hHP hx⟩ : P) ∈ H.subgroupOf P
      from hx)
  · intro hx
    have hxP : x ∈ P := by
      have h1 : (y₀ : G)⁻¹ * (y₀ * x * (y₀ : G)⁻¹) * y₀ ∈ P :=
        mul_mem (mul_mem (inv_mem y₀.2) (hHP hx)) y₀.2
      rwa [show (y₀ : G)⁻¹ * (y₀ * x * (y₀ : G)⁻¹) * y₀ = x by group] at h1
    exact (mem_normalizer_iff.mp hy₀N ⟨x, hxP⟩).mpr hx

theorem EndB.exists_conj_of_two_group {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) {g b : G} (hg2 : g ^ 2 = 1) (hgQ : g ∉ Q)
    (hQg : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hb2 : b ^ 2 = 1) (hbQ : b ∈ Q) (hbg : b * g = g * b)
    (hne : Q ≠ zpowers b) :
    ∃ q ∈ Q, q ∉ zpowers b ∧ (q * g * q⁻¹ = g ∨ q * g * q⁻¹ = b * g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgg : g * g = 1 := by rw [← sq, hg2]
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  have hg2Q : g ^ 2 ∈ Q := by rw [hg2]; exact one_mem _
  have hgN : zpowers g ≤ normalizer (Q : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro q
    refine ⟨fun hq => hQg q hq, fun hq => ?_⟩
    have h1 := hQg _ hq
    rwa [hginv, show g * (g * q * g) * g = (g * g) * q * (g * g) by group, hgg, one_mul,
      mul_one] at h1
  have hP : IsPGroup 2 ↥(Q ⊔ zpowers g) :=
    IsPGroup.to_sup_of_normal_left' hQ (EndB.isPGroup_zpowers_of_sq hg2) hgN
  set H := closure ({b, g} : Set G) with hH
  have hgH : g ∈ H := subset_closure (by simp)
  have hbH : zpowers b ≤ H := zpowers_le.mpr (subset_closure (by simp))
  have hHP : H ≤ Q ⊔ zpowers g := by
    rw [hH, closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact mem_sup_left hbQ
    · exact mem_sup_right (mem_zpowers _)
  have hmemH : ∀ y ∈ H, y = 1 ∨ y = b ∨ y = g ∨ y = b * g := fun y hy =>
    mem_closure_pair hb2 hg2 hbg hy
  have hq₀ : ∃ q₀ ∈ Q, q₀ ∉ zpowers b := by
    by_contra h
    apply hne
    refine le_antisymm (fun q hq => ?_) (zpowers_le.mpr hbQ)
    by_contra hq'
    exact h ⟨q, hq, hq'⟩
  obtain ⟨q₀, hq₀Q, hq₀b⟩ := hq₀
  have hHne : H ≠ Q ⊔ zpowers g := by
    intro h
    have hq₀H : q₀ ∈ H := h ▸ mem_sup_left hq₀Q
    rcases hmemH q₀ hq₀H with h1 | h1 | h1 | h1
    · exact hq₀b (h1 ▸ one_mem _)
    · exact hq₀b (h1 ▸ mem_zpowers b)
    · exact hgQ (h1 ▸ hq₀Q)
    · apply hgQ
      have : g = b⁻¹ * q₀ := by rw [h1]; group
      rw [this]
      exact mul_mem (inv_mem hbQ) hq₀Q
  obtain ⟨y, hyP, hyN, hyH⟩ := EndB.exists_mem_normalizer_of_ne hP hHP hHne
  have hconjH : y * g * y⁻¹ ∈ H := (mem_normalizer_iff.mp hyN g).mp hgH
  have key : ∃ q ∈ Q, q * g * q⁻¹ = y * g * y⁻¹ ∧ (q ∈ H → y ∈ H) := by
    rcases (EndB.mem_sup_zpowers_iff hQg hg2Q).mp hyP with h | h
    · exact ⟨y, h, rfl, id⟩
    · refine ⟨y * g⁻¹, h, by group, fun hq => ?_⟩
      rw [show y = y * g⁻¹ * g by group]
      exact mul_mem hq hgH
  obtain ⟨q, hqQ, hqg, hqH⟩ := key
  refine ⟨q, hqQ, fun h => hyH (hqH (hbH h)), ?_⟩
  rw [hqg]
  rcases hmemH _ hconjH with h | h | h | h
  · exfalso
    apply hgQ
    have : g = y⁻¹ * (y * g * y⁻¹) * y := by group
    rw [this, h, show y⁻¹ * 1 * y = 1 by group]
    exact one_mem _
  · exfalso
    apply hgQ
    have : g = q⁻¹ * (q * g * q⁻¹) * q := by group
    rw [this, hqg, h]
    exact mul_mem (mul_mem (inv_mem hqQ) hbQ) hqQ
  · exact Or.inl h
  · exact Or.inr h

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.LLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* PSL3Four.S}

theorem exists_lambda_Q (hL : LLayer hs π)
    (hQ : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≠
      zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :
    ∃ l ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      l * hs.setup.tBar i j * l⁻¹ =
        betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * hs.setup.tBar i j := by
  have htQ : hs.setup.tBar i j ∉ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    intro h
    obtain ⟨-, hrtS⟩ := hL.rho_t_facts
    exact hrtS ((hL.rho_mem_S_iff _).mpr (mem_sup_right h))
  have hQn : (pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := pCore_normal
  obtain ⟨q, hqQ, hqB, hq⟩ := EndB.exists_conj_of_two_group pCore_isPGroup hs.tBar_sq htQ
    (fun q hq => hQn.conj_mem q hq _) hs.betaBar_sq hs.betaBar_mem_pCore
    (mem_center_iff.mp (betaBar_mem_center _) _).symm hQ
  rcases hq with h | h
  · exfalso
    apply hqB
    rw [← hL.h412.pCore_inf_centralizer]
    refine mem_inf.mpr ⟨hqQ, mem_centralizer_singleton_iff.mpr ?_⟩
    calc q * hs.setup.tBar i j = (q * hs.setup.tBar i j * q⁻¹) * q := by group
      _ = hs.setup.tBar i j * q := by rw [h]
  · exact ⟨q, hqQ, h⟩

theorem exists_conj_zt_of_Q (hL : LLayer hs π)
    (hQ : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≠
      zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (hzM : z ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) :
    ∃ m : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j),
      m * hs.setup.tBar i j * m⁻¹ = QuotientGroup.mk ⟨z, hzM⟩ * hs.setup.tBar i j := by
  obtain ⟨l, -, hl⟩ := hL.exists_lambda_Q hQ
  obtain ⟨v, hv, -, -, hvt⟩ := hs.beta.exists_mem
  have hvM : v ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) := (mem_inf.mp hv).2
  have htM := hs.setup.t_mem_centralizer_beta i j
  have hβM : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈
      centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    mem_centralizer_singleton_iff.mpr rfl
  have htS : t ∈ S := hs.setup.T_le (mem_sup_left (mem_sup_left (mem_zpowers t)))
  have hzt : (QuotientGroup.mk ⟨z, hzM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) *
      hs.setup.tBar i j = hs.setup.tBar i j * QuotientGroup.mk ⟨z, hzM⟩ :=
    EndB.mk_comm hzM htM (hs.setup.z_comm htS).symm
  have hβc : ∀ y : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j),
      y * betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
        betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * y :=
    fun y => mem_center_iff.mp (betaBar_mem_center _) y
  have hbb : betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) *
      betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) = 1 := by
    rw [← sq]; exact hs.betaBar_sq
  rcases hvt with h | h
  · refine ⟨QuotientGroup.mk ⟨v, hvM⟩, ?_⟩
    have h1 : (⟨v, hvM⟩ * ⟨t, htM⟩ * ⟨v, hvM⟩⁻¹ :
        ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) =
        ⟨t, htM⟩ * ⟨z, hzM⟩ := Subtype.ext (by simpa using h)
    have h2 := congrArg (QuotientGroup.mk (s := pPrimeCore 2 _)) h1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h2
    exact h2.trans hzt.symm
  · refine ⟨QuotientGroup.mk ⟨v, hvM⟩ * l, ?_⟩
    have h1 : (⟨v, hvM⟩ * ⟨t, htM⟩ * ⟨v, hvM⟩⁻¹ :
        ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) =
        ⟨t, htM⟩ * ⟨_, hβM⟩ * ⟨z, hzM⟩ := Subtype.ext (by simpa using h)
    have h2 := congrArg (QuotientGroup.mk (s := pPrimeCore 2 _)) h1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h2
    change QuotientGroup.mk ⟨v, hvM⟩ * hs.setup.tBar i j * (QuotientGroup.mk ⟨v, hvM⟩)⁻¹ =
      hs.setup.tBar i j * betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) *
        QuotientGroup.mk ⟨z, hzM⟩ at h2
    calc (QuotientGroup.mk ⟨v, hvM⟩ * l) * hs.setup.tBar i j *
          (QuotientGroup.mk ⟨v, hvM⟩ * l)⁻¹ =
        QuotientGroup.mk ⟨v, hvM⟩ * (l * hs.setup.tBar i j * l⁻¹) *
          (QuotientGroup.mk ⟨v, hvM⟩)⁻¹ := by group
      _ = betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (QuotientGroup.mk ⟨v, hvM⟩ *
          hs.setup.tBar i j * (QuotientGroup.mk ⟨v, hvM⟩)⁻¹) := by
        rw [hl, ← mul_assoc, hβc]; group
      _ = betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (hs.setup.tBar i j *
          betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * QuotientGroup.mk ⟨z, hzM⟩) := by
        rw [h2]
      _ = (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) *
          betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * hs.setup.tBar i j *
            QuotientGroup.mk ⟨z, hzM⟩ := by
        rw [hβc (hs.setup.tBar i j)]; group
      _ = QuotientGroup.mk ⟨z, hzM⟩ * hs.setup.tBar i j := by rw [hbb, one_mul, hzt]

end EndB.LLayer

end CFSG.ComponentClassification.HarrisLit
