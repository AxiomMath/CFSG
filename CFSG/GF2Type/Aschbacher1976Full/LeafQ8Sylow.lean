module

public import CFSG.GF2Type.Aschbacher1976Full.Defs
import CFSG.Holt.TwoGroups
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cAut
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8Tools

public section

namespace CFSG.GF2Type.Aschbacher1976Full.LeafQ8

open CFSG CFSG.Blueprint

section Q8

open QuaternionGroup

theorem q8_central {q : QuaternionGroup 2} (h : ∀ r, q * r = r * q) : q = 1 ∨ q = a 2 := by
  revert q; decide +kernel

theorem q8_sq {q : QuaternionGroup 2} (h : q ^ 2 = 1) : q = 1 ∨ q = a 2 := by
  revert q; decide +kernel

theorem q8_a2_comm (q : QuaternionGroup 2) : a 2 * q = q * a 2 := by
  revert q; decide +kernel

theorem q8_inner_of_central_twist (σ : QuaternionGroup 2 →* QuaternionGroup 2)
    (h : ∀ q, σ q = q ∨ σ q = q * a 2) : ∃ g : QuaternionGroup 2, ∀ q, σ q = g * q * g⁻¹ := by
  have key : ∀ u v : QuaternionGroup 2, (u = a 1 ∨ u = a 1 * a 2) → (v = xa 0 ∨ v = xa 0 * a 2) →
      ∃ g : QuaternionGroup 2, g * a 1 * g⁻¹ = u ∧ g * xa 0 * g⁻¹ = v := by decide +kernel
  obtain ⟨g, hg1, hg2⟩ := key (σ (a 1)) (σ (xa 0)) (h _) (h _)
  refine ⟨g, fun q => ?_⟩
  have e1 := CFSG.ClassicalInvolution.q8Eval_eq σ q
  have e2 := CFSG.ClassicalInvolution.q8Eval_eq (MulAut.conj g).toMonoidHom q
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e2
  rw [e1, ← hg1, ← hg2, ← e2]

theorem q8_not_comm : (a 1 : QuaternionGroup 2) * xa 0 ≠ xa 0 * a 1 := by decide

theorem not_isCyclic_of_q8 {P : Type*} [Group P] (φ : QuaternionGroup 2 →* P)
    (hφ : Function.Injective φ) : ¬ IsCyclic P := by
  intro hP
  have hc : IsMulCommutative P := inferInstance
  exact q8_not_comm (hφ (by rw [map_mul, map_mul]; exact hc.is_comm.comm _ _))

theorem isEmpty_mulEquiv_dihedral_of_q8 {P : Type*} [Group P] (φ : QuaternionGroup 2 →* P)
    (hφ : Function.Injective φ) (m : ℕ) : IsEmpty (P ≃* DihedralGroup (2 ^ m)) := by
  refine ⟨fun ψ => ?_⟩
  have hrot : ∀ x : DihedralGroup (2 ^ m), orderOf x = 4 → ∃ i, x = DihedralGroup.r i := by
    intro x hx
    cases x with
    | r i => exact ⟨i, rfl⟩
    | sr i => rw [DihedralGroup.orderOf_sr] at hx; omega
  have hinj : Function.Injective (ψ.toMonoidHom.comp φ) := ψ.injective.comp hφ
  obtain ⟨i, hi⟩ := hrot ((ψ.toMonoidHom.comp φ) (a 1)) (by
    rw [orderOf_injective _ hinj]; simpa using (QuaternionGroup.orderOf_a_one (n := 2)))
  obtain ⟨j, hj⟩ := hrot ((ψ.toMonoidHom.comp φ) (xa 0)) (by
    rw [orderOf_injective _ hinj]; exact QuaternionGroup.orderOf_xa (n := 2) 0)
  refine q8_not_comm (hinj ?_)
  rw [map_mul, map_mul, hi, hj, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]

end Q8

section Basic

variable {G : Type} [Group G] [Finite G] {z : G}

theorem mem_Hz_iff {h : G} : h ∈ Hz z ↔ z * h = h * z := by
  simp [Hz, Subgroup.mem_centralizer_iff]

theorem Fz_le_Hz (z : G) : Fz z ≤ Hz z := Subgroup.map_subtype_le _

theorem Fz_conj_mem {h f : G} (hh : h ∈ Hz z) (hf : f ∈ Fz z) : h * f * h⁻¹ ∈ Fz z := by
  obtain ⟨f', hf', rfl⟩ := hf
  exact ⟨⟨h, hh⟩ * f' * ⟨h, hh⟩⁻¹,
    (CFSG.LocalCores.generalized_fitting_characteristic).2.conj_mem f' hf' ⟨h, hh⟩, rfl⟩

theorem mem_Fz_of_centralizes {h : G} (hh : h ∈ Hz z) (hc : ∀ f ∈ Fz z, h * f = f * h) :
    h ∈ Fz z := by
  have h1 : (⟨h, hh⟩ : Hz z) ∈ Subgroup.centralizer
      ((generalizedFitting (Hz z) : Subgroup (Hz z)) : Set (Hz z)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f' hf'
    exact Subtype.ext (hc f' ⟨f', hf', rfl⟩).symm
  exact ⟨_, CFSG.centralizer_generalizedFitting_le (Hz z) h1, rfl⟩

theorem z_mem_Hz (z : G) : z ∈ Hz z := mem_Hz_iff.mpr rfl

theorem z_mem_Fz (z : G) : z ∈ Fz z :=
  mem_Fz_of_centralizes (z_mem_Hz z) fun f hf => mem_Hz_iff.mp (Fz_le_Hz z hf)

theorem e_central (e : ↥(Fz z) ≃* QuaternionGroup 2) {f : G} (hf : f ∈ Fz z)
    (hc : ∀ g ∈ Fz z, f * g = g * f) : ∀ r, e ⟨f, hf⟩ * r = r * e ⟨f, hf⟩ := by
  intro r
  obtain ⟨g, rfl⟩ := e.surjective r
  rw [← map_mul, ← map_mul]
  exact congrArg e (Subtype.ext (hc g g.2))

theorem e_z (hz : orderOf z = 2) (e : ↥(Fz z) ≃* QuaternionGroup 2) :
    e ⟨z, z_mem_Fz z⟩ = QuaternionGroup.a 2 := by
  have hz1 : z ≠ 1 := by rintro rfl; simp at hz
  rcases q8_central (e_central e (z_mem_Fz z) fun g hg => mem_Hz_iff.mp (Fz_le_Hz z hg)) with h | h
  · exact absurd (congrArg Subtype.val (e.injective (h.trans (map_one e).symm))) hz1
  · exact h

theorem eq_one_or_eq_z (hz : orderOf z = 2) (e : ↥(Fz z) ≃* QuaternionGroup 2) {f : G}
    (hf : f ∈ Fz z) (hc : ∀ g ∈ Fz z, f * g = g * f) : f = 1 ∨ f = z := by
  rcases q8_central (e_central e hf hc) with h | h
  · exact Or.inl (congrArg Subtype.val (e.injective (h.trans (map_one e).symm)))
  · exact Or.inr (congrArg Subtype.val (e.injective (h.trans (e_z hz e).symm)))

theorem eq_one_or_eq_z_of_sq (hz : orderOf z = 2) (e : ↥(Fz z) ≃* QuaternionGroup 2) {f : G}
    (hf : f ∈ Fz z) (h2 : f ^ 2 = 1) : f = 1 ∨ f = z := by
  have h : (e ⟨f, hf⟩) ^ 2 = 1 := by
    rw [← map_pow, ← map_one e]; exact congrArg e (Subtype.ext h2)
  rcases q8_sq h with h | h
  · exact Or.inl (congrArg Subtype.val (e.injective (h.trans (map_one e).symm)))
  · exact Or.inr (congrArg Subtype.val (e.injective (h.trans (e_z hz e).symm)))

theorem exists_maximal_two_subgroup (hF : IsPGroup 2 (Fz z)) :
    ∃ T : Subgroup G, IsPGroup 2 T ∧ Fz z ≤ T ∧ T ≤ Hz z ∧
      ∀ Q : Subgroup G, IsPGroup 2 Q → T ≤ Q → Q ≤ Hz z → Q = T := by
  obtain ⟨T, hFT, hT⟩ := Set.Finite.exists_le_maximal
    (s := {Q : Subgroup G | IsPGroup 2 Q ∧ Fz z ≤ Q ∧ Q ≤ Hz z}) (Set.toFinite _)
    ⟨hF, le_rfl, Fz_le_Hz z⟩
  obtain ⟨hT2, -, hTH⟩ := hT.1
  exact ⟨T, hT2, hFT, hTH, fun Q hQ hTQ hQH =>
    le_antisymm (hT.2 ⟨hQ, hFT.trans hTQ, hQH⟩ hTQ) hTQ⟩

theorem eq_one_or_eq_z_of_central (hz : orderOf z = 2) (e : ↥(Fz z) ≃* QuaternionGroup 2)
    {T : Subgroup G} (hFT : Fz z ≤ T) (hTH : T ≤ Hz z) {t : G} (ht : t ∈ T)
    (hc : ∀ s ∈ T, t * s = s * t) : t = 1 ∨ t = z :=
  eq_one_or_eq_z hz e (mem_Fz_of_centralizes (hTH ht) fun f hf => hc f (hFT hf))
    fun g hg => hc g (hFT hg)

theorem normalizer_le_Hz (hz : orderOf z = 2) (e : ↥(Fz z) ≃* QuaternionGroup 2)
    {T : Subgroup G} (hFT : Fz z ≤ T) (hTH : T ≤ Hz z) :
    Subgroup.normalizer (T : Set G) ≤ Hz z := by
  intro x hx
  rw [mem_Hz_iff]
  have hz1 : z ≠ 1 := by rintro rfl; simp at hz
  have hx' := Subgroup.mem_normalizer_iff.mp hx
  have h1 : x * z * x⁻¹ ∈ T := (hx' z).mp (hFT (z_mem_Fz z))
  have h2 : ∀ s ∈ T, (x * z * x⁻¹) * s = s * (x * z * x⁻¹) := by
    intro s hs
    have hs' : x⁻¹ * s * x ∈ T := by
      refine (hx' _).mpr ?_
      have : x * (x⁻¹ * s * x) * x⁻¹ = s := by group
      rwa [this]
    have hcomm := mem_Hz_iff.mp (hTH hs')
    calc (x * z * x⁻¹) * s = x * (z * (x⁻¹ * s * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * s * x) * z) * x⁻¹ := by rw [hcomm]
      _ = s * (x * z * x⁻¹) := by group
  rcases eq_one_or_eq_z_of_central hz e hFT hTH h1 h2 with h | h
  · exact absurd (by simpa using h) hz1
  · exact (mul_inv_eq_iff_eq_mul.mp h).symm

theorem Hz_le_normalizer (z : G) : Hz z ≤ Subgroup.normalizer ((Fz z : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro f
  refine ⟨fun hf => Fz_conj_mem hh hf, fun hf => ?_⟩
  have h1 := Fz_conj_mem ((Hz z).inv_mem hh) hf
  have h2 : h⁻¹ * (h * f * h⁻¹) * h⁻¹⁻¹ = f := by group
  rwa [h2] at h1

@[expose] noncomputable def rho (z : G) : ↥(Hz z) →* MulAut ↥(Fz z) :=
  (Fz z).normalizerMonoidHom.comp (Subgroup.inclusion (Hz_le_normalizer z))

theorem card_Hz_dvd (hz : orderOf z = 2) (e : ↥(Fz z) ≃* QuaternionGroup 2) :
    Nat.card (Hz z) ∣ 48 := by
  have h1 : Nat.card (Hz z) = Nat.card (rho z).range * Nat.card (rho z).ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (rho z).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (rho z)).toEquiv]
  have h2 : Nat.card (rho z).range ∣ 24 := by
    rw [← CFSG.GH74.GLS.Stage2.Signalizer.Odd87.natCard_mulAut_of_quaternion e]
    exact Subgroup.card_subgroup_dvd_card _
  have h3 : Nat.card (rho z).ker ∣ 2 := by
    have hle : (rho z).ker ≤ Subgroup.zpowers (⟨z, z_mem_Hz z⟩ : Hz z) := by
      intro k hk
      have hk' : ∀ f ∈ Fz z, (k : G) * f = f * (k : G) := by
        intro f hf
        have h4 : (k : G) * f * (k : G)⁻¹ = f :=
          congrArg (fun m : MulAut ↥(Fz z) => ((m ⟨f, hf⟩ : ↥(Fz z)) : G)) (MonoidHom.mem_ker.mp hk)
        exact mul_inv_eq_iff_eq_mul.mp h4
      have hkF := mem_Fz_of_centralizes k.2 hk'
      rcases eq_one_or_eq_z hz e hkF (fun g hg => hk' g hg) with h | h
      · rw [show k = 1 from Subtype.ext h]; exact Subgroup.one_mem _
      · rw [show k = ⟨z, z_mem_Hz z⟩ from Subtype.ext h]; exact Subgroup.mem_zpowers _
    calc Nat.card (rho z).ker ∣ Nat.card (Subgroup.zpowers (⟨z, z_mem_Hz z⟩ : Hz z)) :=
          Subgroup.card_dvd_of_le hle
      _ = 2 := by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hz]
  rw [h1]
  simpa using mul_dvd_mul h2 h3

theorem no_normal_four (hz : orderOf z = 2) (e : ↥(Fz z) ≃* QuaternionGroup 2) {T : Subgroup G}
    (hTp : IsPGroup 2 T) (hFT : Fz z ≤ T) (hTH : T ≤ Hz z) :
    ∀ V : Subgroup T, V.Normal → CFSG.Open.IsElemAbelian 2 V → Nat.card V ≠ 4 := by
  intro V hVn hVe hV4
  have hzT : z ∈ T := hFT (z_mem_Fz z)
  have hVF : ∀ x ∈ V, (x : G) ∈ Fz z → (x : G) = 1 ∨ (x : G) = z := fun x hx hxF =>
    eq_one_or_eq_z_of_sq hz e hxF (by simpa using congrArg Subtype.val (hVe.2 x hx))
  have hzV : (⟨z, hzT⟩ : T) ∈ V := by
    have : Group.IsNilpotent T := hTp.isNilpotent
    have hVbot : V ≠ ⊥ := by rintro rfl; simp at hV4
    obtain ⟨⟨c, hc⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hVbot)
    obtain ⟨hcV, hcZ⟩ := Subgroup.mem_inf.mp hc
    rcases eq_one_or_eq_z_of_central hz e hFT hTH c.2 (fun s hs =>
        (congrArg Subtype.val (Subgroup.mem_center_iff.mp hcZ ⟨s, hs⟩)).symm) with h | h
    · exact absurd (Subtype.ext (Subtype.ext h)) hc1
    · rwa [show c = ⟨z, hzT⟩ from Subtype.ext h] at hcV
  obtain ⟨v, hvV, hvF⟩ : ∃ v ∈ V, (v : G) ∉ Fz z := by
    by_contra hcon
    push Not at hcon
    have hle : V ≤ Subgroup.zpowers (⟨z, hzT⟩ : T) := by
      intro x hx
      rcases hVF x hx (hcon x hx) with h | h
      · rw [show x = 1 from Subtype.ext h]; exact Subgroup.one_mem _
      · rw [show x = ⟨z, hzT⟩ from Subtype.ext h]; exact Subgroup.mem_zpowers _
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hz, hV4] at this
    omega
  have hcomm : ∀ f ∈ Fz z, (v : G) * f * (v : G)⁻¹ = f ∨ (v : G) * f * (v : G)⁻¹ = z * f := by
    intro f hf
    have hfT : f ∈ T := hFT hf
    have h1 : (v * ⟨f, hfT⟩ * v⁻¹ * ⟨f, hfT⟩⁻¹ : T) ∈ V := by
      have h2 := V.mul_mem hvV (hVn.conj_mem v⁻¹ (V.inv_mem hvV) ⟨f, hfT⟩)
      rwa [show v * (⟨f, hfT⟩ * v⁻¹ * ⟨f, hfT⟩⁻¹ : T) = v * ⟨f, hfT⟩ * v⁻¹ * ⟨f, hfT⟩⁻¹ by
        group] at h2
    have h2 : (v : G) * f * (v : G)⁻¹ * f⁻¹ ∈ Fz z :=
      (Fz z).mul_mem (Fz_conj_mem (hTH v.2) hf) ((Fz z).inv_mem hf)
    rcases hVF _ h1 h2 with h | h
    · exact Or.inl (mul_inv_eq_one.mp h)
    · exact Or.inr (mul_inv_eq_iff_eq_mul.mp h)
  let σ : QuaternionGroup 2 →* QuaternionGroup 2 :=
    (MulAut.congr e (rho z ⟨v, hTH v.2⟩)).toMonoidHom
  have hσ : ∀ q, σ q = q ∨ σ q = q * QuaternionGroup.a 2 := by
    intro q
    obtain ⟨f, rfl⟩ := e.surjective q
    have hσf : σ (e f) = e (rho z ⟨v, hTH v.2⟩ f) := by simp [σ, MulAut.congr_apply]
    rcases hcomm f f.2 with h | h
    · exact Or.inl (by rw [hσf, show rho z ⟨v, hTH v.2⟩ f = f from Subtype.ext h])
    · refine Or.inr ?_
      rw [hσf, show rho z ⟨v, hTH v.2⟩ f = ⟨z, z_mem_Fz z⟩ * f from Subtype.ext h, map_mul,
        e_z hz e, q8_a2_comm]
  obtain ⟨g₀, hg₀⟩ := q8_inner_of_central_twist σ hσ
  have hconj : ∀ f ∈ Fz z, (v : G) * f * (v : G)⁻¹ = (e.symm g₀ : G) * f * (e.symm g₀ : G)⁻¹ := by
    intro f hf
    have h1 := hg₀ (e ⟨f, hf⟩)
    have hσf : σ (e ⟨f, hf⟩) = e (rho z ⟨v, hTH v.2⟩ ⟨f, hf⟩) := by
      simp [σ, MulAut.congr_apply]
    rw [hσf] at h1
    have h2 : rho z ⟨v, hTH v.2⟩ ⟨f, hf⟩ = e.symm g₀ * ⟨f, hf⟩ * (e.symm g₀)⁻¹ := by
      apply e.injective
      rw [h1, map_mul, map_mul, map_inv, e.apply_symm_apply]
    exact congrArg Subtype.val h2
  have hgF : ((e.symm g₀ : ↥(Fz z)) : G) ∈ Fz z := (e.symm g₀).2
  have hu : ((e.symm g₀ : ↥(Fz z)) : G)⁻¹ * v ∈ Fz z := by
    refine mem_Fz_of_centralizes ((Hz z).mul_mem ((Hz z).inv_mem (Fz_le_Hz z hgF)) (hTH v.2)) ?_
    intro f hf
    have h1 := hconj f hf
    calc ((e.symm g₀ : ↥(Fz z)) : G)⁻¹ * v * f
        = ((e.symm g₀ : ↥(Fz z)) : G)⁻¹ * ((v : G) * f * (v : G)⁻¹) * v := by group
      _ = ((e.symm g₀ : ↥(Fz z)) : G)⁻¹ * (((e.symm g₀ : ↥(Fz z)) : G) * f *
            ((e.symm g₀ : ↥(Fz z)) : G)⁻¹) * v := by rw [h1]
      _ = f * (((e.symm g₀ : ↥(Fz z)) : G)⁻¹ * v) := by group
  exact hvF (by simpa using (Fz z).mul_mem hgF hu)

theorem exists_sylow_shape (hz : orderOf z = 2) (hsymp : IsPGroup 2 (Fz z))
    (e : ↥(Fz z) ≃* QuaternionGroup 2) :
    ∃ S : Sylow 2 G, z ∈ (S : Subgroup G) ∧
      ((∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥(S : Subgroup G) ≃* CFSG.Open.SemidihedralGroup n)) ∨
        ∃ n : ℕ, 3 ≤ n ∧ Nonempty (↥(S : Subgroup G) ≃* QuaternionGroup (2 ^ (n - 2)))) := by
  obtain ⟨T, hTp, hFT, hTH, hTmax⟩ := exists_maximal_two_subgroup hsymp
  obtain ⟨S, hS⟩ := CFSG.EvenSmallLie.OmegaEight.Child8.exists_sylow_eq_of_normalizer_le
    hTp hTmax (normalizer_le_Hz hz e hFT hTH)
  refine ⟨S, hS ▸ hFT (z_mem_Fz z), ?_⟩
  let φ : QuaternionGroup 2 →* ↥T := (Subgroup.inclusion hFT).comp e.symm.toMonoidHom
  have hφ : Function.Injective φ := (Subgroup.inclusion_injective hFT).comp e.symm.injective
  have eST : ↥(S : Subgroup G) ≃* ↥T := MulEquiv.subgroupCongr hS
  rcases CFSG.Holt.cyclic_or_dihedral_or_semidihedral_or_quaternion_of_no_normal_four hTp
      (no_normal_four hz e hTp hFT hTH) with hcyc | ⟨m, -, ⟨ψ⟩⟩ | ⟨n, hn, ⟨ψ⟩⟩ | ⟨n, hn, ⟨ψ⟩⟩
  · exact (not_isCyclic_of_q8 φ hφ hcyc).elim
  · exact ((isEmpty_mulEquiv_dihedral_of_q8 φ hφ m).false ψ).elim
  · exact Or.inl ⟨n, hn, ⟨eST.trans ψ⟩⟩
  · exact Or.inr ⟨n, hn, ⟨eST.trans ψ⟩⟩

end Basic

end CFSG.GF2Type.Aschbacher1976Full.LeafQ8
