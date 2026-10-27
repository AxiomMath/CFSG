module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Z
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Omega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

namespace Sec2

section Psi

variable {G : Type} [Group G] {Q : Subgroup G} {z : G} {ψ : G → (Fin 6 → ZMod 2)}

omit [Group G] in
theorem conj_zpow_eq {H : Type*} [Group H] {d z : H} (h : d * z = z * d) (k : ℤ) :
    d * z ^ k * d⁻¹ = z ^ k := by
  rw [(Commute.zpow_right h k).eq, mul_inv_cancel_right]

theorem psi_one (hadd : ∀ a ∈ Q, ∀ b ∈ Q, ψ (a * b) = ψ a + ψ b) : ψ 1 = 0 := by
  have h := hadd 1 Q.one_mem 1 Q.one_mem
  rw [mul_one] at h
  have : ψ 1 + ψ 1 = ψ 1 + 0 := by rw [← h, add_zero]
  exact add_left_cancel this

theorem psi_mul_inv (hadd : ∀ a ∈ Q, ∀ b ∈ Q, ψ (a * b) = ψ a + ψ b) {a b : G} (ha : a ∈ Q)
    (hb : b ∈ Q) : ψ (a * b⁻¹) = ψ a - ψ b := by
  have h := hadd (a * b⁻¹) (Q.mul_mem ha (Q.inv_mem hb)) b hb
  rw [inv_mul_cancel_right] at h
  rw [h, add_sub_cancel_right]

theorem psi_eq_iff (hadd : ∀ a ∈ Q, ∀ b ∈ Q, ψ (a * b) = ψ a + ψ b)
    (hker : ∀ a ∈ Q, ψ a = 0 ↔ a ∈ zpowers z) {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) :
    ψ a = ψ b ↔ a * b⁻¹ ∈ zpowers z := by
  rw [← hker _ (Q.mul_mem ha (Q.inv_mem hb)), psi_mul_inv hadd ha hb, sub_eq_zero]

end Psi

section Transport

variable {G : Type} [Group G] {Q : Subgroup G} {z : G} {ψ : G → (Fin 6 → ZMod 2)}
  (hadd : ∀ a ∈ Q, ∀ b ∈ Q, ψ (a * b) = ψ a + ψ b)
  (hsurj : ∀ v : Fin 6 → ZMod 2, ∃ a ∈ Q, ψ a = v)
  (hker : ∀ a ∈ Q, ψ a = 0 ↔ a ∈ zpowers z)

noncomputable def lift (v : Fin 6 → ZMod 2) : G := Classical.choose (hsurj v)

theorem lift_mem (v : Fin 6 → ZMod 2) : lift hsurj v ∈ Q := (Classical.choose_spec (hsurj v)).1

theorem psi_lift (v : Fin 6 → ZMod 2) : ψ (lift hsurj v) = v :=
  (Classical.choose_spec (hsurj v)).2

include hadd hker in
theorem psi_conj_eq {d : G} (hdN : d ∈ normalizer (Q : Set G))
    (hdz : d ∈ centralizer ({z} : Set G)) {a b : G} (ha : a ∈ Q) (hb : b ∈ Q)
    (hab : ψ a = ψ b) : ψ (d * a * d⁻¹) = ψ (d * b * d⁻¹) := by
  rw [psi_eq_iff hadd hker ha hb] at hab
  have hda := (mem_normalizer_iff.mp hdN a).mp ha
  have hdb := (mem_normalizer_iff.mp hdN b).mp hb
  rw [psi_eq_iff hadd hker hda hdb]
  have e : d * a * d⁻¹ * (d * b * d⁻¹)⁻¹ = d * (a * b⁻¹) * d⁻¹ := by group
  rw [e]
  obtain ⟨k, hk⟩ := hab
  rw [← hk]
  exact ⟨k, (conj_zpow_eq (mem_centralizer_singleton_iff.mp hdz) k).symm⟩

noncomputable def act (d : G) (v : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  ψ (d * lift hsurj v * d⁻¹)

include hadd hker in
theorem act_psi {d : G} (hdN : d ∈ normalizer (Q : Set G)) (hdz : d ∈ centralizer ({z} : Set G))
    {a : G} (ha : a ∈ Q) : act hsurj d (ψ a) = ψ (d * a * d⁻¹) :=
  psi_conj_eq hadd hker hdN hdz (lift_mem hsurj _) ha (psi_lift hsurj _)

include hadd hker in
theorem act_mul {d e : G} (hdN : d ∈ normalizer (Q : Set G))
    (hdz : d ∈ centralizer ({z} : Set G)) (heN : e ∈ normalizer (Q : Set G))
    (hez : e ∈ centralizer ({z} : Set G)) (v : Fin 6 → ZMod 2) :
    act hsurj (d * e) v = act hsurj d (act hsurj e v) := by
  obtain ⟨a, ha, rfl⟩ := hsurj v
  have hea := (mem_normalizer_iff.mp heN a).mp ha
  rw [act_psi hadd hsurj hker (mul_mem hdN heN) (mul_mem hdz hez) ha,
    act_psi hadd hsurj hker heN hez ha, act_psi hadd hsurj hker hdN hdz hea]
  congr 1
  group

include hadd hker in
theorem act_one (v : Fin 6 → ZMod 2) : act hsurj 1 v = v := by
  obtain ⟨a, ha, rfl⟩ := hsurj v
  rw [act_psi hadd hsurj hker (one_mem _) (one_mem _) ha]
  congr 1
  group

end Transport

end Sec2

namespace Sec2Q

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F T₀ Q : Subgroup G}
  {u y z : G}

theorem M_le_normalizer (hQ : Sec2Q G A R g E F T₀ Q u y z) :
    sec2M Q (sec2T E T₀) ≤ normalizer (Q : Set G) :=
  Sec2.sec2M_le_normalizer hQ.T_le_normalizer

theorem normalizer_le_centralizer (hQ : Sec2Q G A R g E F T₀ Q u y z) :
    normalizer (Q : Set G) ≤ centralizer ({z} : Set G) := by
  intro n hn
  have h := Sec2.mem_normalizer_centerIn hn
  rw [hQ.centerIn_Q] at h
  have := Sec2.conj_eq_of_mem_normalizer_zpowers hQ.order h
  rw [mem_centralizer_singleton_iff]
  calc n * z = n * z * n⁻¹ * n := by group
    _ = z * n := by rw [this]

theorem eq_zpowers_or_eq_of_le_normalizer (h216 : Step216) (hQ : Sec2Q G A R g E F T₀ Q u y z)
    {B : Subgroup G} (hzB : zpowers z ≤ B) (hBQ : B ≤ Q)
    (hMB : sec2M Q (sec2T E T₀) ≤ normalizer (B : Set G)) : B = zpowers z ∨ B = Q := by
  obtain ⟨ψ, ρ, hadd, hsurj, hker, -, hρ, hrange, -⟩ := h216 G A R g E F T₀ Q u y z hQ
  let W : Submodule (ZMod 2) (Fin 6 → ZMod 2) :=
    { carrier := {v | ∃ b ∈ B, ψ b = v}
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a * b, B.mul_mem ha hb, hadd a (hBQ ha) b (hBQ hb)⟩
      zero_mem' := ⟨1, B.one_mem, Sec2.psi_one hadd⟩
      smul_mem' := by
        rintro c _ ⟨b, hb, rfl⟩
        rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one c with rfl | rfl
        · exact ⟨1, B.one_mem, by rw [zero_smul, Sec2.psi_one hadd]⟩
        · exact ⟨b, hb, (one_smul _ _).symm⟩ }
  have hW : ∀ γ ∈ Open.timmesfeldOmega qMinus, ∀ w ∈ W, γ w ∈ W := by
    rintro γ hγ _ ⟨b, hb, rfl⟩
    rw [← hrange] at hγ
    obtain ⟨m, rfl⟩ := hγ
    refine ⟨(m : G) * b * (m : G)⁻¹, (mem_normalizer_iff.mp (hMB m.2) b).mp hb, ?_⟩
    exact hρ m b (hBQ hb)
  rcases Sec2Omega.eq_bot_or_eq_top_of_timmesfeldOmega hW with h | h
  · left
    refine le_antisymm (fun b hb => ?_) hzB
    have hbW : ψ b ∈ W := ⟨b, hb, rfl⟩
    rw [h, Submodule.mem_bot] at hbW
    exact (hker b (hBQ hb)).mp hbW
  · right
    refine le_antisymm hBQ fun a ha => ?_
    have haW : ψ a ∈ W := h ▸ Submodule.mem_top
    obtain ⟨b, hb, hba⟩ := haW
    have h1 := (Sec2.psi_eq_iff hadd hker ha (hBQ hb)).mp hba.symm
    have := B.mul_mem (hzB h1) hb
    rwa [inv_mul_cancel_right] at this

theorem derived_acts_nontrivially (h216 : Step216) (hQ : Sec2Q G A R g E F T₀ Q u y z) :
    ∀ B : Subgroup G, zpowers z ≤ B → B < Q → sec2M Q (sec2T E T₀) ≤ normalizer (B : Set G) →
      ∀ n : ℕ, ∃ k ∈ (derivedSeries (sec2M Q (sec2T E T₀)) n).map (sec2M Q (sec2T E T₀)).subtype,
        ∃ x ∈ Q, k⁻¹ * x * k * x⁻¹ ∉ B := by
  intro B hzB hBQ hMB n
  have hB : B = zpowers z := by
    rcases hQ.eq_zpowers_or_eq_of_le_normalizer h216 hzB hBQ.le hMB with h | h
    · exact h
    · exact absurd h hBQ.ne
  subst hB
  obtain ⟨ψ, ρ, hadd, hsurj, hker, -, hρ, hrange, -⟩ := h216 G A R g E F T₀ Q u y z hQ
  obtain ⟨k, hk, hk1⟩ := Sec2Omega.exists_mem_derivedSeries_ne_one ρ hrange n
  have hk' : k⁻¹ ∈ derivedSeries (sec2M Q (sec2T E T₀)) n := inv_mem hk
  have hk1' : ρ k⁻¹ ≠ 1 := by
    rw [map_inv]
    exact fun h => hk1 (inv_eq_one.mp h)
  obtain ⟨v, hv⟩ : ∃ v, ρ k⁻¹ v ≠ v := by
    by_contra h
    push Not at h
    exact hk1' (LinearEquiv.ext h)
  obtain ⟨a, ha, rfl⟩ := hsurj v
  refine ⟨(k : G), ⟨k, hk, rfl⟩, a, ha, fun hmem => hv ?_⟩
  have hkN := hQ.M_le_normalizer k.2
  have hka : (k : G)⁻¹ * a * (k : G) ∈ Q := by
    have := (mem_normalizer_iff.mp (inv_mem hkN) a).mp ha
    simpa using this
  have h1 := (Sec2.psi_eq_iff hadd hker hka ha).mpr hmem
  have h2 := hρ k⁻¹ a ha
  simp only [coe_inv, inv_inv] at h2
  rw [← h2, h1]

theorem acts_trivially_of_isPGroup (h216 : Step216) (hQ : Sec2Q G A R g E F T₀ Q u y z)
    {D : Subgroup G} (hD : IsPGroup 2 D) (hDN : D ≤ normalizer (Q : Set G))
    (hDz : D ≤ centralizer ({z} : Set G))
    (hinv : ∀ m ∈ sec2M Q (sec2T E T₀), ∀ a ∈ Q, (∀ d ∈ D, d * a * d⁻¹ * a⁻¹ ∈ zpowers z) →
      ∀ d ∈ D, d * (m * a * m⁻¹) * d⁻¹ * (m * a * m⁻¹)⁻¹ ∈ zpowers z) :
    ∀ d ∈ D, ∀ a ∈ Q, d * a * d⁻¹ * a⁻¹ ∈ zpowers z := by
  obtain ⟨ψ, ρ, hadd, hsurj, hker, -, -, -, -⟩ := h216 G A R g E F T₀ Q u y z hQ
  have hzQ := hQ.z_mem_Q
  let B : Subgroup G :=
    { carrier := {a | a ∈ Q ∧ ∀ d ∈ D, d * a * d⁻¹ * a⁻¹ ∈ zpowers z}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Q.mul_mem ha hb, fun d hd => ?_⟩
        have e : d * (a * b) * d⁻¹ * (a * b)⁻¹ =
            (d * a * d⁻¹ * a⁻¹) * (a * (d * b * d⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        refine mul_mem (ha' d hd) ?_
        obtain ⟨k, hk⟩ := hb' d hd
        rw [← hk]
        exact ⟨k, (Sec2.conj_zpow_eq (mem_centralizer_iff.mp hQ.z_mem_centralizer_Q a ha)
          k).symm⟩
      one_mem' := ⟨Q.one_mem, fun d _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Q.inv_mem ha, fun d hd => ?_⟩
        have e : d * a⁻¹ * d⁻¹ * a⁻¹⁻¹ = a⁻¹ * (d * a * d⁻¹ * a⁻¹)⁻¹ * a := by group
        rw [e]
        obtain ⟨k, hk⟩ := inv_mem (ha' d hd)
        rw [← hk]
        refine ⟨k, ?_⟩
        have h := Sec2.conj_zpow_eq
          (mem_centralizer_iff.mp hQ.z_mem_centralizer_Q a⁻¹ (Q.inv_mem ha)) k
        rw [inv_inv] at h
        exact h.symm }
  have hzB : zpowers z ≤ B := by
    rw [zpowers_le]
    refine ⟨hzQ, fun d hd => ?_⟩
    rw [mem_centralizer_singleton_iff.mp (hDz hd), mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hMB : sec2M Q (sec2T E T₀) ≤ normalizer (B : Set G) := by
    intro m hm
    have hmN := hQ.M_le_normalizer hm
    refine mem_normalizer_iff.mpr fun a => ⟨fun ha => ⟨(mem_normalizer_iff.mp hmN a).mp ha.1,
      hinv m hm a ha.1 ha.2⟩, fun ha => ?_⟩
    have ha1 : a ∈ Q := (mem_normalizer_iff.mp hmN a).mpr ha.1
    have hm' : m⁻¹ ∈ sec2M Q (sec2T E T₀) := inv_mem hm
    have h := hinv m⁻¹ hm' (m * a * m⁻¹) ha.1 ha.2
    have e : m⁻¹ * (m * a * m⁻¹) * m⁻¹⁻¹ = a := by group
    rw [e] at h
    exact ⟨ha1, h⟩
  rcases hQ.eq_zpowers_or_eq_of_le_normalizer h216 hzB (fun a ha => ha.1) hMB with h | h
  ·
    exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let σ : ↥D →* Equiv.Perm (Fin 6 → ZMod 2) :=
      { toFun := fun d =>
          { toFun := Sec2.act hsurj (d : G)
            invFun := Sec2.act hsurj (d : G)⁻¹
            left_inv := fun v => by
              rw [← Sec2.act_mul hadd hsurj hker (inv_mem (hDN d.2)) (inv_mem (hDz d.2))
                (hDN d.2) (hDz d.2), inv_mul_cancel, Sec2.act_one hadd hsurj hker]
            right_inv := fun v => by
              rw [← Sec2.act_mul hadd hsurj hker (hDN d.2) (hDz d.2) (inv_mem (hDN d.2))
                (inv_mem (hDz d.2)), mul_inv_cancel, Sec2.act_one hadd hsurj hker] }
        map_one' := Equiv.ext fun v => Sec2.act_one hadd hsurj hker v
        map_mul' := fun d e => Equiv.ext fun v =>
          Sec2.act_mul hadd hsurj hker (hDN d.2) (hDz d.2) (hDN e.2) (hDz e.2) v }
    let _ : MulAction ↥D (Fin 6 → ZMod 2) := MulAction.compHom _ σ
    have hmod := hD.card_modEq_card_fixedPoints (Fin 6 → ZMod 2)
    have h64 : Nat.card (Fin 6 → ZMod 2) = 64 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
      norm_num
    rw [h64] at hmod
    have h0 : (0 : Fin 6 → ZMod 2) ∈ MulAction.fixedPoints ↥D (Fin 6 → ZMod 2) := by
      intro d
      change Sec2.act hsurj (d : G) 0 = 0
      rw [← Sec2.psi_one hadd, Sec2.act_psi hadd hsurj hker (hDN d.2) (hDz d.2) Q.one_mem,
        mul_one, mul_inv_cancel]
    have hfin : Nat.card (MulAction.fixedPoints ↥D (Fin 6 → ZMod 2)) ≠ 1 := by
      intro h1
      rw [h1] at hmod
      exact absurd hmod (by decide)
    obtain ⟨v, hv, hv0⟩ : ∃ v ∈ MulAction.fixedPoints ↥D (Fin 6 → ZMod 2), v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hfin
      rw [Nat.card_eq_one_iff_exists]
      exact ⟨⟨0, h0⟩, fun w => Subtype.ext (hcon w w.2)⟩
    obtain ⟨a, ha, rfl⟩ := hsurj v
    have haB : a ∈ B := by
      refine ⟨ha, fun d hd => ?_⟩
      have h1 := hv ⟨d, hd⟩
      change Sec2.act hsurj d (ψ a) = ψ a at h1
      rw [Sec2.act_psi hadd hsurj hker (hDN hd) (hDz hd) ha] at h1
      exact (Sec2.psi_eq_iff hadd hker ((mem_normalizer_iff.mp (hDN hd) a).mp ha) ha).mp h1
    rw [h] at haB
    exact hv0 ((hker a ha).mpr haB)
  · intro d hd a ha
    have : a ∈ B := h ▸ ha
    exact this.2 d hd

end Sec2Q

end CFSG.ComponentClassification.AS81
