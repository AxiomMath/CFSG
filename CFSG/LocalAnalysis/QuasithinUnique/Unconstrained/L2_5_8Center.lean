module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Small
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.NotationAPI

public section

namespace CFSG.QuasithinUnique.Unc25Small

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}

theorem center_K_trivial (N : Notation25 hs) (hsimple : IsSimpleGroup ↥N.K) :
    ∀ x ∈ N.K, (∀ y ∈ N.K, y * x = x * y) → x = 1 := by
  intro x hx hxc
  obtain ⟨a, b, hab⟩ := exists_noncomm_K N
  have hcen : (⟨x, hx⟩ : ↥N.K) ∈ Subgroup.center ↥N.K := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hxc y y.2)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥N.K) with h | h
  · rw [h, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  · exfalso
    have : a ∈ Subgroup.center ↥N.K := by rw [h]; exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp this b).symm)

theorem K0_inf_SC_eq_bot (N : Notation25 hs)
    (hZ : ∀ x ∈ N.K, (∀ y ∈ N.K, y * x = x * y) → x = 1)
    (hshape : N.K0 = N.K ∨ ∃ s ∈ N.S, CFSG.conjugate N.K s ≠ N.K ∧
      N.K0 = N.K ⊔ CFSG.conjugate N.K s ∧ ⁅N.K, CFSG.conjugate N.K s⁆ = ⊥) :
    N.K0 ⊓ N.SC = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxK0, hxSC⟩ := hx
  have hxc : ∀ v ∈ N.K0, v * x = x * v := fun v hv =>
    Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer hxSC) v hv
  rw [Subgroup.mem_bot]
  rcases hshape with h | ⟨s, hsS, hne, hK0, hcomm⟩
  · rw [h] at hxK0 hxc
    exact hZ x hxK0 hxc
  · rw [hK0] at hxK0 hxc
    have hc : ∀ a ∈ N.K, ∀ b ∈ CFSG.conjugate N.K s, a * b = b * a := fun a ha b hb =>
      BenderBranch.commute_of_commutator_eq_bot hcomm ha hb
    obtain ⟨a, ha, b, hb, rfl⟩ := (BenderBranch.mem_sup_iff_of_commute hc).mp hxK0
    have haK : ∀ w ∈ N.K, w * a = a * w := by
      intro w hw
      have h1 := hxc w (Subgroup.mem_sup_left hw)
      have hbw : b * w = w * b := (hc w hw b hb).symm
      have : w * a * b = a * w * b := by
        calc w * a * b = w * (a * b) := by rw [mul_assoc]
          _ = (a * b) * w := h1
          _ = a * (b * w) := by rw [mul_assoc]
          _ = a * (w * b) := by rw [hbw]
          _ = a * w * b := by rw [mul_assoc]
      exact mul_right_cancel this
    have ha1 : a = 1 := hZ a ha haK
    subst ha1
    rw [one_mul]
    have hbK' : ∀ w ∈ CFSG.conjugate N.K s, w * b = b * w := by
      intro w hw
      have h1 := hxc w (Subgroup.mem_sup_right hw)
      simpa using h1
    have hcK : s * b * s⁻¹ ∈ N.K := BenderBranch.mem_conjugate_iff.mp hb
    have hcc : ∀ w ∈ N.K, w * (s * b * s⁻¹) = (s * b * s⁻¹) * w := by
      intro w hw
      have hw' : s⁻¹ * w * s ∈ CFSG.conjugate N.K s := by
        rw [BenderBranch.mem_conjugate_iff]
        simpa [mul_assoc] using hw
      have := hbK' _ hw'
      calc w * (s * b * s⁻¹) = s * ((s⁻¹ * w * s) * b) * s⁻¹ := by group
        _ = s * (b * (s⁻¹ * w * s)) * s⁻¹ := by rw [this]
        _ = (s * b * s⁻¹) * w := by group
    have hc1 : s * b * s⁻¹ = 1 := hZ _ hcK hcc
    calc b = s⁻¹ * (s * b * s⁻¹) * s := by group
      _ = 1 := by rw [hc1]; group

theorem mem_conj_of_centralizes (N : Notation25 hs)
    (hZ : ∀ x ∈ N.K, (∀ y ∈ N.K, y * x = x * y) → x = 1) {s₀ : G}
    (hK0 : N.K0 = N.K ⊔ CFSG.conjugate N.K s₀) (hcomm : ⁅N.K, CFSG.conjugate N.K s₀⁆ = ⊥)
    {y : G} (hy : y ∈ N.K0) (hyc : ∀ w ∈ N.K, w * y = y * w) : y ∈ CFSG.conjugate N.K s₀ := by
  have hc : ∀ a ∈ N.K, ∀ b ∈ CFSG.conjugate N.K s₀, a * b = b * a := fun a ha b hb =>
    BenderBranch.commute_of_commutator_eq_bot hcomm ha hb
  rw [hK0] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := (BenderBranch.mem_sup_iff_of_commute hc).mp hy
  have haK : ∀ w ∈ N.K, w * a = a * w := by
    intro w hw
    have h1 := hyc w hw
    have hbw : b * w = w * b := (hc w hw b hb).symm
    have : w * a * b = a * w * b := by
      calc w * a * b = w * (a * b) := by rw [mul_assoc]
        _ = (a * b) * w := h1
        _ = a * (b * w) := by rw [mul_assoc]
        _ = a * (w * b) := by rw [hbw]
        _ = a * w * b := by rw [mul_assoc]
    exact mul_right_cancel this
  have ha1 : a = 1 := hZ a ha haK
  subst ha1
  rwa [one_mul]

theorem inf_conj_eq_one (N : Notation25 hs)
    (hZ : ∀ x ∈ N.K, (∀ y ∈ N.K, y * x = x * y) → x = 1) {s₀ : G}
    (hcomm : ⁅N.K, CFSG.conjugate N.K s₀⁆ = ⊥) {x : G} (hxK : x ∈ N.K)
    (hxK' : x ∈ CFSG.conjugate N.K s₀) : x = 1 :=
  hZ x hxK fun _ hw => BenderBranch.commute_of_commutator_eq_bot hcomm hw hxK'

theorem conj_eq_or_eq (N : Notation25 hs)
    (hZ : ∀ x ∈ N.K, (∀ y ∈ N.K, y * x = x * y) → x = 1) {s₀ : G}
    (hK0 : N.K0 = N.K ⊔ CFSG.conjugate N.K s₀) (hcomm : ⁅N.K, CFSG.conjugate N.K s₀⁆ = ⊥) :
    ∀ t ∈ N.S, CFSG.conjugate N.K t = N.K ∨ CFSG.conjugate N.K t = CFSG.conjugate N.K s₀ := by
  intro t ht
  have hcomp : IsComponentIn (CFSG.conjugate N.K t) N.H :=
    Unc25G2.isComponentIn_conjugate N.isComp (N.S_le_H ht)
  rcases BenderBranch.eq_or_commute_of_isComponentIn N.isComp hcomp with h | h
  · left
    exact h.symm
  · right
    have hle0 : CFSG.conjugate N.K t ≤ N.K0 :=
      le_iSup (fun s : N.S => N.K.map (MulAut.conj (s : G)).toMonoidHom)
        ⟨t⁻¹, N.S.inv_mem ht⟩
    have hle : CFSG.conjugate N.K t ≤ CFSG.conjugate N.K s₀ := fun y hy =>
      mem_conj_of_centralizes N hZ hK0 hcomm (hle0 hy) fun w hw =>
        BenderBranch.commute_of_commutator_eq_bot h hw hy
    exact Subgroup.eq_of_le_of_card_ge hle
      ((BenderBranch.card_conjugate N.K s₀).le.trans (BenderBranch.card_conjugate N.K t).ge)

theorem mem_normalizer_of_mem_centerOf (N : Notation25 hs)
    (hZ : ∀ x ∈ N.K, (∀ y ∈ N.K, y * x = x * y) → x = 1) (hy : ∃ y ∈ N.SK, y ≠ 1) :
    ∀ s ∈ centerOf N.S, s ∈ Subgroup.normalizer (N.K : Set G) := by
  intro s hs'
  have hsS : s ∈ N.S := hs'.1
  have hcent : ∀ t ∈ N.S, t * s = s * t := fun t ht =>
    Subgroup.mem_centralizer_iff.mp hs'.2 t ht
  have hcompL : IsComponentIn (CFSG.conjugate N.K s⁻¹) N.H :=
    Unc25G2.isComponentIn_conjugate N.isComp (N.H.inv_mem (N.S_le_H hsS))
  rcases BenderBranch.eq_or_commute_of_isComponentIn N.isComp hcompL with h | h
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : s * x * s⁻¹ ∈ N.K ↔ s * x * s⁻¹ ∈ CFSG.conjugate N.K s⁻¹ := by rw [← h]
    rw [key, BenderBranch.mem_conjugate_iff]
    have : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
    rw [this]
  · exfalso
    obtain ⟨y, hySK, hy1⟩ := hy
    apply hy1
    have hyS : y ∈ N.S := hySK.1
    have hyK : y ∈ N.K := hySK.2
    have hys : y * s = s * y := hcent y hyS
    have hyL : y ∈ CFSG.conjugate N.K s⁻¹ := by
      rw [BenderBranch.mem_conjugate_iff]
      have : s⁻¹ * y * s⁻¹⁻¹ = y := by
        calc s⁻¹ * y * s⁻¹⁻¹ = s⁻¹ * (y * s) := by group
          _ = s⁻¹ * (s * y) := by rw [hys]
          _ = y := by group
      rw [this]
      exact hyK
    exact hZ y hyK fun w hw => BenderBranch.commute_of_commutator_eq_bot h hw hyL

theorem exists_inner_e (N : Notation25 hs)
    (hshape : N.K0 = N.K ∨ ∃ s ∈ N.S, CFSG.conjugate N.K s ≠ N.K ∧
      N.K0 = N.K ⊔ CFSG.conjugate N.K s ∧ ⁅N.K, CFSG.conjugate N.K s⁆ = ⊥)
    {s : G} (hsZ : s ∈ centerOf N.S) {u : G} (huSK : u ∈ N.SK)
    (hu : ∀ x ∈ N.K, s * x * s⁻¹ = u * x * u⁻¹) :
    ∃ e ∈ N.S ⊓ N.K0, ∀ x ∈ N.K0, s * x * s⁻¹ = e * x * e⁻¹ := by
  rcases hshape with h | ⟨s₀, hs₀S, hne, hK0, hcomm⟩
  · refine ⟨u, ⟨huSK.1, ?_⟩, fun x hx => hu x (h ▸ hx)⟩
    rw [h]
    exact huSK.2
  · have hc : ∀ a ∈ N.K, ∀ b ∈ CFSG.conjugate N.K s₀, a * b = b * a := fun a ha b hb =>
      BenderBranch.commute_of_commutator_eq_bot hcomm ha hb
    have hs₀s : s₀ * s = s * s₀ := Subgroup.mem_centralizer_iff.mp hsZ.2 s₀ hs₀S
    have huS : u ∈ N.S := huSK.1
    have huK : u ∈ N.K := huSK.2
    set u' : G := s₀⁻¹ * u * s₀ with hu'
    have hu'K' : u' ∈ CFSG.conjugate N.K s₀ := by
      rw [BenderBranch.mem_conjugate_iff]
      have : s₀ * u' * s₀⁻¹ = u := by rw [hu']; group
      rw [this]
      exact huK
    have hu'S : u' ∈ N.S :=
      N.S.mul_mem (N.S.mul_mem (N.S.inv_mem hs₀S) huS) hs₀S
    refine ⟨u * u', ⟨N.S.mul_mem huS hu'S, ?_⟩, fun x hx => ?_⟩
    · refine N.K0.mul_mem (N.K_le_K0 huK) ?_
      rw [hK0]
      exact Subgroup.mem_sup_right hu'K'
    · rw [hK0] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := (BenderBranch.mem_sup_iff_of_commute hc).mp hx
      have hA : s * a * s⁻¹ = u * a * u⁻¹ := hu a ha
      have hB : s * b * s⁻¹ = u' * b * u'⁻¹ := by
        have hk : s₀ * b * s₀⁻¹ ∈ N.K := BenderBranch.mem_conjugate_iff.mp hb
        have h1 := hu _ hk
        have hcs : s₀⁻¹ * s * s₀ = s := by
          calc s₀⁻¹ * s * s₀ = s₀⁻¹ * (s * s₀) := by group
            _ = s₀⁻¹ * (s₀ * s) := by rw [hs₀s]
            _ = s := by group
        calc s * b * s⁻¹ = (s₀⁻¹ * s * s₀) * b * (s₀⁻¹ * s * s₀)⁻¹ := by rw [hcs]
          _ = s₀⁻¹ * (s * (s₀ * b * s₀⁻¹) * s⁻¹) * s₀ := by group
          _ = s₀⁻¹ * (u * (s₀ * b * s₀⁻¹) * u⁻¹) * s₀ := by rw [h1]
          _ = u' * b * u'⁻¹ := by rw [hu']; group
      have h1 : u' * a = a * u' := (hc a ha u' hu'K').symm
      have h2 : (u' * b * u'⁻¹) * u⁻¹ = u⁻¹ * (u' * b * u'⁻¹) :=
        (hc u⁻¹ (N.K.inv_mem huK) _
          ((CFSG.conjugate N.K s₀).mul_mem ((CFSG.conjugate N.K s₀).mul_mem hu'K' hb)
            ((CFSG.conjugate N.K s₀).inv_mem hu'K'))).symm
      calc s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
        _ = (u * a * u⁻¹) * (u' * b * u'⁻¹) := by rw [hA, hB]
        _ = u * a * (u⁻¹ * (u' * b * u'⁻¹)) := by group
        _ = u * a * ((u' * b * u'⁻¹) * u⁻¹) := by rw [h2]
        _ = u * (a * u') * b * u'⁻¹ * u⁻¹ := by group
        _ = u * (u' * a) * b * u'⁻¹ * u⁻¹ := by rw [h1]
        _ = (u * u') * (a * b) * (u * u')⁻¹ := by group

theorem center_decomp_aux (N : Notation25 hs) (hK0SC : N.K0 ⊓ N.SC = ⊥)
    (hex : ∀ s ∈ centerOf N.S, ∃ e ∈ N.S ⊓ N.K0, ∀ x ∈ N.K0, s * x * s⁻¹ = e * x * e⁻¹) :
    centerOf N.S = (centerOf N.S ⊓ N.SK0) ⊔ (centerOf N.S ⊓ N.SC) := by
  refine le_antisymm (fun s hs' => ?_) (sup_le inf_le_left inf_le_left)
  obtain ⟨e, he, hact⟩ := hex s hs'
  have hsS : s ∈ N.S := hs'.1
  have hcentS : ∀ t ∈ N.S, t * s = s * t := fun t ht =>
    Subgroup.mem_centralizer_iff.mp hs'.2 t ht
  obtain ⟨c, hc⟩ : ∃ c : G, c = e⁻¹ * s := ⟨_, rfl⟩
  have hs_ec : s = e * c := by rw [hc]; group
  have hcS : c ∈ N.S := by rw [hc]; exact N.S.mul_mem (N.S.inv_mem he.1) hsS
  have hcC : c ∈ Subgroup.centralizer (N.K0 : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := hact x hx
    calc x * c = e⁻¹ * (e * x * e⁻¹) * s := by rw [hc]; group
      _ = e⁻¹ * (s * x * s⁻¹) * s := by rw [this]
      _ = c * x := by rw [hc]; group
  have hcSC : c ∈ N.SC := ⟨hcS, hcC⟩
  have heZ : e ∈ centerOf N.S := by
    refine ⟨he.1, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    have h1 : t * s * t⁻¹ = s := by rw [hcentS t ht]; group
    have h2 : t * e * t⁻¹ ∈ N.K0 :=
      (Subgroup.mem_normalizer_iff.mp (N.S_le_normalizer_K0 ht) e).mp he.2
    have h3 : e⁻¹ * (t * e * t⁻¹) = c * (t * c * t⁻¹)⁻¹ := by
      calc e⁻¹ * (t * e * t⁻¹) = e⁻¹ * (t * (e * c) * t⁻¹) * (t * c * t⁻¹)⁻¹ := by group
        _ = e⁻¹ * (t * s * t⁻¹) * (t * c * t⁻¹)⁻¹ := by rw [← hs_ec]
        _ = e⁻¹ * s * (t * c * t⁻¹)⁻¹ := by rw [h1]
        _ = c * (t * c * t⁻¹)⁻¹ := by rw [hc]
    have h4 : t * c * t⁻¹ ∈ N.SC :=
      (Subgroup.mem_normalizer_iff.mp (N.S_le_normalizer_SC ht) c).mp hcSC
    have h5 : e⁻¹ * (t * e * t⁻¹) ∈ N.K0 ⊓ N.SC := by
      refine ⟨N.K0.mul_mem (N.K0.inv_mem he.2) h2, ?_⟩
      rw [h3]
      exact N.SC.mul_mem hcSC (N.SC.inv_mem h4)
    rw [hK0SC, Subgroup.mem_bot] at h5
    calc t * e = (t * e * t⁻¹) * t := by group
      _ = (e * (e⁻¹ * (t * e * t⁻¹))) * t := by group
      _ = e * t := by rw [h5]; group
  have hcZ : c ∈ centerOf N.S := by
    rw [hc]
    exact (centerOf N.S).mul_mem ((centerOf N.S).inv_mem heZ) hs'
  rw [hs_ec]
  exact Subgroup.mul_mem_sup ⟨heZ, he⟩ ⟨hcZ, hcSC⟩

end CFSG.QuasithinUnique.Unc25Small
