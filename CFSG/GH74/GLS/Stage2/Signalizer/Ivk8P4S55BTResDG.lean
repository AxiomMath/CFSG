module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResDF
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTE16
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResDE

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResD

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ}
  {H P : Subgroup G} {g : G} {X Y : Subgroup G} {t : G} {q : ℕ} {I Q₁ : Subgroup G}

theorem exists_conj_to_z (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {w : G} (hw : w = z ∨ w = t) :
    ∃ w' c : G, ((w = z ∧ w' = t) ∨ (w = t ∧ w' = z)) ∧ c * w * c⁻¹ = z ∧
      c * w' * c⁻¹ ∈ S := by
  have hu := hd.u.udata
  rcases hw with hw | hw
  · exact ⟨t, 1, Or.inl ⟨hw, rfl⟩, by rw [hw]; group, by simpa using hd.u.t_mem⟩
  · obtain ⟨c₀, hc₀⟩ := isConj_iff.mp hu.conj_zt
    have hsC : c₀⁻¹ * z * c₀ ∈ Cen z := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hzt : z * t = t * z := hu.comm
      rw [← hc₀] at hzt
      calc c₀⁻¹ * z * c₀ * z = c₀⁻¹ * (z * (c₀ * z * c₀⁻¹)) * c₀ := by group
        _ = c₀⁻¹ * ((c₀ * z * c₀⁻¹) * z) * c₀ := by rw [hzt]
        _ = z * (c₀⁻¹ * z * c₀) := by group
    have hs2 : c₀⁻¹ * z * c₀ * (c₀⁻¹ * z * c₀) = 1 := by
      calc c₀⁻¹ * z * c₀ * (c₀⁻¹ * z * c₀) = c₀⁻¹ * (z * z) * c₀ := by group
        _ = 1 := by rw [hu.z_sq]; group
    obtain ⟨d, hdC, hdS⟩ := exists_conj_mem_of_sylow h.ctx.sylow hsC hs2
    refine ⟨z, d * c₀⁻¹, Or.inr ⟨hw, rfl⟩, ?_, ?_⟩
    · rw [hw, ← hc₀]
      have hdz : d * z = z * d := Subgroup.mem_centralizer_singleton_iff.mp hdC
      calc d * c₀⁻¹ * (c₀ * z * c₀⁻¹) * (d * c₀⁻¹)⁻¹ = d * z * d⁻¹ := by group
        _ = z * d * d⁻¹ := by rw [hdz]
        _ = z := by group
    · have e : d * c₀⁻¹ * z * (d * c₀⁻¹)⁻¹ = d * (c₀⁻¹ * z * c₀) * d⁻¹ := by group
      rw [e]
      exact hdS

omit [Finite G] in
theorem pair_facts (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {w w' : G}
    (hww : (w = z ∧ w' = t) ∨ (w = t ∧ w' = z)) :
    w ∈ L52Two.U4 z t ∧ w' ∈ L52Two.U4 z t ∧ L52Two.U4 w w' = L52Two.U4 z t ∧ w' ≠ w ∧
      IsConj z w' ∧ ¬ IsConj z (w * w') ∧ w * w = 1 := by
  have hu := hd.u.udata
  have hz : z ∈ L52Two.U4 z t := Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
  have ht : t ∈ L52Two.U4 z t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  rcases hww with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · exact ⟨hz, ht, rfl, hu.zt_ne.symm, hu.conj_zt, hu.not_conj, hu.z_sq⟩
  · refine ⟨ht, hz, sup_comm _ _, hu.zt_ne, IsConj.refl z, ?_, hu.t_sq⟩
    rw [← hu.comm]
    exact hu.not_conj

omit [Finite G] in
theorem pLayerOf_le' (X : Subgroup G) : pLayerOf 2 X ≤ X := sSup_le fun _ hL => hL.1

theorem ixz_conj (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {w w' c : G}
    (hww : (w = z ∧ w' = t) ∨ (w = t ∧ w' = z)) (hcw : c * w * c⁻¹ = z) :
    Ixz z (c * w' * c⁻¹ * z) =
      (pLayerOf 2 (centralizer ((L52Two.U4 z t : Subgroup G) : Set G))).map
        (MulAut.conj c).toMonoidHom := by
  obtain ⟨-, -, hUeq, -, -, -, hw2⟩ := pair_facts hd hww
  have e1 : ({c * w' * c⁻¹ * z, z} : Set G) = {c * (w' * w) * c⁻¹, c * w * c⁻¹} := by
    rw [← hcw]
    congr 1
    group
  have e2 : centralizer ({w' * w, w} : Set G) =
      centralizer ((L52Two.U4 z t : Subgroup G) : Set G) := by
    rw [← L52Two.centralizer_U4_eq hw2, hUeq]
  unfold Ixz
  rw [e1, ← map_centralizer_pair_conj, e2, pLayerOf_map_conj]

theorem diagAt_of_conj (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {w w' c : G}
    (hww : (w = z ∧ w' = t) ∨ (w = t ∧ w' = z)) (hcw : c * w * c⁻¹ = z)
    (hcS : c * w' * c⁻¹ ∈ S) :
    DiagAt z k S (c * w' * c⁻¹) (I.map (MulAut.conj c).toMonoidHom)
      ((pPrimeCoreOf 2 (pLayerOf 2 (centralizer ((L52Two.U4 z t : Subgroup G) : Set G)))).map
        (MulAut.conj c).toMonoidHom)
      ((pPrimeCoreOf 2 H ⊓ centralizer ({w} : Set G)).map (MulAut.conj c).toMonoidHom) := by
  obtain ⟨hwU, hw'U, -, hne, hw'c, hnc, -⟩ := pair_facts hd hww
  have hIU : ∀ i ∈ I, ∀ u ∈ L52Two.U4 z t, i * u = u * i := fun i hi u hu =>
    (hd.i.good.comm i hi u hu).symm
  have hL₀U : ∀ l ∈ pLayerOf 2 (centralizer ((L52Two.U4 z t : Subgroup G) : Set G)),
      ∀ u ∈ L52Two.U4 z t, l * u = u * l := fun l hl u hu =>
    (Subgroup.mem_centralizer_iff.mp (pLayerOf_le' _ hl) u hu).symm
  have hIxz := ixz_conj hd hww hcw
  refine ⟨h.ctx, h.two, hcS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hcw]
    intro he
    exact hne (mul_left_cancel (mul_right_cancel he))
  · exact hw'c.trans (isConj_iff.mpr ⟨c, rfl⟩)
  · intro hc'
    apply hnc
    have e : z * (c * w' * c⁻¹) = c * (w * w') * c⁻¹ := by rw [← hcw]; group
    rw [e] at hc'
    exact hc'.trans (isConj_iff.mpr ⟨c⁻¹, by group⟩)
  · rintro _ ⟨i, hi, rfl⟩
    rw [← hcw]
    exact conj_mem_centralizer (Subgroup.mem_centralizer_singleton_iff.mpr (hIU i hi w hwU)) c
  · rintro _ ⟨i, hi, rfl⟩
    exact conj_mem_centralizer (Subgroup.mem_centralizer_singleton_iff.mpr (hIU i hi w' hw'U)) c
  · rw [← Subgroup.map_commutator, hd.i.perf]
  · rintro _ ⟨o, ho, rfl⟩
    rw [← hcw]
    exact conj_mem_centralizer (Subgroup.mem_centralizer_singleton_iff.mpr
      (hL₀U o (TwoThin.pPrimeCoreOf_le _ ho) w hwU)) c
  · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact TwoThin.card_pPrimeCoreOf_odd _
  · intro l hl o ho
    rw [hIxz] at hl
    obtain ⟨l₀, hl₀, rfl⟩ := hl
    obtain ⟨o₀, ho₀, rfl⟩ := ho
    exact ⟨l₀ * o₀ * l₀⁻¹, TwoThin.pPrimeCoreOf_normalized _ hl₀ ho₀, by
      rw [map_mul, map_mul, map_inv]⟩
  · intro l hl
    rw [hIxz] at hl
    obtain ⟨l₀, hl₀, rfl⟩ := hl
    obtain ⟨i, hi, o, ho, he⟩ := cover_of_surj hd.i.surj l₀ hl₀
    exact ⟨_, ⟨i, hi, rfl⟩, _, ⟨o, ho, rfl⟩, by rw [he, map_mul]⟩
  · rintro _ ⟨o, ho, rfl⟩
    rw [← hcw]
    exact conj_mem_centralizer ho.2 c
  · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd H) (Subgroup.card_dvd_of_le inf_le_left)
  · rintro _ ⟨i, hi, rfl⟩ _ ⟨o, ho, rfl⟩
    have hiw : i ∈ centralizer ({w} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hIU i hi w hwU)
    refine ⟨i * o * i⁻¹, ⟨TwoThin.pPrimeCoreOf_normalized H (hd.i.good.le_H hi) ho.1, ?_⟩, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hiw ho.2) (Subgroup.inv_mem _ hiw)
    · rw [map_mul, map_mul, map_inv]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResD
