module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2BCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma65
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Cent

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}

structure OuterB (L : Subgroup G) (t : G) (B : Subgroup G) (β : G) : Prop where
  B_le : B ≤ L
  B_cent : B ≤ centralizer ({t} : Set G)
  B_iso : Nonempty (↥B ≃* alternatingGroup (Fin 5))
  beta_mem : β ∈ B
  beta_order : orderOf β = 3
  D_quot : Nonempty (↥(L ⊓ centralizer ({β} : Set G)) ⧸
    fusionOddCore ↥(L ⊓ centralizer ({β} : Set G)) ≃* alternatingGroup (Fin 6))
  D_odd : fusionOddCoreOf (L ⊓ centralizer ({β} : Set G)) ≤ zpowers β

theorem OuterB.exists_of_betaDataSqB (hB : BetaDataSqB ↥L) {t : G} (htL : t ∈ L)
    (ht2 : orderOf t = 2) (hsq : ∃ g ∈ L, g * g = t) :
    ∃ (B : Subgroup G) (β : G), OuterB L t B β := by
  classical
  let t' : ↥L := ⟨t, htL⟩
  have ht'2 : orderOf t' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact ht2
  obtain ⟨g, hgL, hg⟩ := hsq
  have hsq' : ∃ g' : ↥L, g' * g' = t' := ⟨⟨g, hgL⟩, Subtype.ext hg⟩
  obtain ⟨B, β, hBt, ⟨eB⟩, hβB, hβ⟩ := hB t' ht'2 hsq'
  obtain ⟨hβ3, hD, hO⟩ := hβ.transport (MulEquiv.refl ↥L)
  refine ⟨B.map L.subtype, ((β : ↥L) : G), ?_⟩
  refine
  { B_le := ?_
    B_cent := ?_
    B_iso := ⟨((B.equivMapOfInjective L.subtype L.subtype_injective)).symm.trans eB⟩
    beta_mem := ⟨β, hβB, rfl⟩
    beta_order := hβ3
    D_quot := hD
    D_odd := hO }
  · rintro _ ⟨b, hb, rfl⟩
    exact b.2
  · rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have := congrArg Subtype.val (mem_centralizer_singleton_iff.1 (hBt hb))
    exact this

namespace OuterE

variable (h : OuterE G L z t T E)

include h in
theorem cent_cent_z (hzt : ∃ y : G, y * z * y⁻¹ = z * t) (hW : WFacts L t E) {v : G}
    (hv : v ∈ centralizer (E : Set G)) (hvz : v * z = z * v) :
    v = 1 ∨ v = z ∨ v = t ∨ v = t * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvH : v ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hvz
  have hsq : v * v ∈ L ⊔ zpowers z := h.cfg.sq_mem_sup hvH
  obtain ⟨l, hl, c, hc, hvvlc⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (zpowers_le.2 h.cfg.z_cent) hsq
  have hzC : z ∈ centralizer (E : Set G) := h.zpowers_le_cent_E (mem_zpowers z)
  have hcC : c ∈ centralizer (E : Set G) := by
    rcases mem_zpowers_sq_eq_one h.cfg.z_sq hc with rfl | rfl
    · exact one_mem _
    · exact hzC
  have hlC : l ∈ centralizer (E : Set G) := by
    have : l = v * v * c⁻¹ := by rw [hvvlc]; group
    rw [this]
    exact mul_mem (mul_mem hv hv) (inv_mem hcC)
  have hl' : l = 1 ∨ l = t :=
    hW.cent l hl (fun e he => (mem_centralizer_iff.1 hlC e he).symm)
  have hlz : l * c = c * l := by
    rcases mem_zpowers_sq_eq_one h.cfg.z_sq hc with rfl | rfl <;> rcases hl' with rfl | rfl
    · simp
    · simp
    · simp
    · exact h.cfg.t_comm_z
  have hl2 : l * l = 1 := by
    rcases hl' with rfl | rfl
    · simp
    · exact h.cfg.t_sq
  have hc2 : c * c = 1 := by
    rcases mem_zpowers_sq_eq_one h.cfg.z_sq hc with rfl | rfl
    · simp
    · exact h.cfg.z_sq
  have hv4 : v ^ 4 = 1 := by
    calc v ^ 4 = (v * v) * (v * v) := by
          rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
      _ = (l * c) * (l * c) := by rw [hvvlc]
      _ = (l * l) * (c * c) := by
        calc l * c * (l * c) = l * (c * l) * c := by group
          _ = l * (l * c) * c := by rw [hlz]
          _ = (l * l) * (c * c) := by group
      _ = 1 := by rw [hl2, hc2, one_mul]
  have hord : orderOf v ∣ 4 := orderOf_dvd_of_pow_eq_one hv4
  have hpg : IsPGroup 2 (zpowers v) := by
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show orderOf v ∣ 2 ^ 2 by norm_num; exact hord)
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have hle := h.le_of_two_group hzt hpg (zpowers_le.2 hv) (zpowers_le.2 hvH) (mem_zpowers v)
  have hzt_cent : zpowers t ≤ centralizer (zpowers z : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    exact ((show Commute z t from h.cfg.t_comm_z.symm).zpow_left k).eq
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_centralizer hzt_cent hle
  rcases mem_zpowers_sq_eq_one h.cfg.z_sq ha with rfl | rfl <;>
    rcases mem_zpowers_sq_eq_one h.cfg.t_sq hb with rfl | rfl
  · exact Or.inl (by simpa using hab)
  · exact Or.inr (Or.inr (Or.inl (by simpa using hab)))
  · exact Or.inr (Or.inl (by simpa using hab))
  · exact Or.inr (Or.inr (Or.inr (by rw [hab]; exact h.cfg.t_comm_z.symm)))

include h in
theorem B_centralizes_S (hzt : ∃ y : G, y * z * y⁻¹ = z * t) (hW : WFacts L t E)
    (haut : Nat.card (MulAut ↥E) = 1920) (hT : Nat.card ↥T = 512) {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (hTQ : T ≤ Q) {x : G} (hxQ : x ∈ Q) (hxT : x ∉ T)
    (hxN : x ∈ normalizer (T : Set G)) {B : Subgroup G} {β : G} (hB : OuterB L t B β)
    {S : Subgroup G} (hS2 : IsPGroup 2 S) (hSC : S ≤ centralizer (E : Set G))
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S)
    (hzS : z ∈ S) : ∀ b ∈ B, ∀ s ∈ S, b * s = s * b := by
  have hV := fun v hv hvz => h.cent_cent_z hzt hW (v := v) hv hvz
  have hzL : ∀ a ∈ L, a * z = z * a := fun a ha => h.cfg.z_comm_of_mem_A ha
  rcases h.sylow_centralizer_shape' hzt haut hT hQ hTQ hxQ hxT hxN hS2 hSC hSmax hzS with
    ⟨k, hk, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · have : Group.IsSolvable (MulAut ↥S) := isSolvable_mulAut_of_dihedral hk e
    exact B_centralizes_S_gen hW hzL h.cfg.t_comm_z hB.B_le hB.B_cent hB.B_iso hS2 hSC hSmax hzS
      hV
  · have : Group.IsSolvable (MulAut ↥S) := isSolvable_mulAut_congr e (semidihedralAutSolvable n hn)
    exact B_centralizes_S_gen hW hzL h.cfg.t_comm_z hB.B_le hB.B_cent hB.B_iso hS2 hSC hSmax hzS
      hV

end OuterE

end CFSG.EvenSporadicStandard.Fin76b
