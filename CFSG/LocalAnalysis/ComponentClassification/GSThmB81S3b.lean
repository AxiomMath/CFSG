module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S3a
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81S3

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr Seven

theorem Three81.conj_ne_mul_of_odd {G : Type*} [Group G] {a y w : G} (ho : Odd (orderOf y))
    (hya : y * a = a * y) (ha : orderOf a = 2) : y * w * y⁻¹ ≠ a * w := by
  intro h
  have hk : ∀ n : ℕ, y ^ n * w * (y ^ n)⁻¹ = a ^ n * w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hyan : y * a ^ n * y⁻¹ = a ^ n := by
        rw [← conj_pow, show y * a * y⁻¹ = a by rw [hya]; group]
      calc y ^ (n + 1) * w * (y ^ (n + 1))⁻¹ = y * (y ^ n * w * (y ^ n)⁻¹) * y⁻¹ := by
            rw [pow_succ']; group
        _ = (y * a ^ n * y⁻¹) * (y * w * y⁻¹) := by rw [ih]; group
        _ = a ^ (n + 1) * w := by rw [hyan, h, pow_succ]; group
  have h1 := hk (orderOf y)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, right_eq_mul] at h1
  have h2 : 2 ∣ orderOf y := ha ▸ orderOf_dvd_of_pow_eq_one h1
  exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr h2)

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

theorem exists_lieModel_J_sq (H₁ : h.L81Hyp) : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
    Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p (2 * f) := by
  obtain ⟨-, p, f, hp, hp2, hf, -, hJt⟩ := Hyp52.Sec8Case.exists_params h.toHyp52 H₁.case8
  rcases hJt with hL | ⟨-, -, hA⟩
  · exact ⟨p, f, hp, hp2, hf, hL⟩
  · exact ⟨3, 1, Nat.prime_three, by norm_num, le_rfl, Or.inl ⟨by decide,
      CFSG.LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six _
        hA⟩⟩

namespace Data

variable {H₁ : h.L81Hyp} (d : Data H₁)

abbrev Y3 : Subgroup H := centralizer ({h.a} : Set H) ⊓ centralizer ({d.b * d.z} : Set H)

theorem comm_of_odd_of_le_Y3 (hCent : CF81L2Cent2Nilp) {Q : Subgroup H} (hQ : IsPGroup 2 Q)
    (hQY : Q ≤ d.Y3) {y : H} (hyY : y ∈ d.Y3) (ho : Odd (orderOf y))
    (hyQ : ∀ w ∈ Q, y * w * y⁻¹ ∈ Q) {q : H} (hq : q ∈ Q) : y * q = q * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYN : d.Y3 ≤ normalizer (h.J : Set H) := inf_le_left.trans H₁.centralizer_le_normalizer_J
  obtain ⟨p', f', hp', hp2', hf', hJL⟩ := H₁.exists_lieModel_J_sq
  have hΓ := hCent _ p' f' hp' hp2' hf' hJL _ d.orderOf_zbar
  rw [← rhoE_of_mem_J d.z_mem_J] at hΓ
  have hzN : d.z ∈ normalizer (h.J : Set H) := le_normalizer d.z_mem_J
  have hbN : d.b ∈ normalizer (h.J : Set H) := (mem_inf.mp (h.S_le d.b_mem_S)).2
  have hρb : rhoE h.J d.b = 1 := (rhoE_eq_one_iff hbN).mpr (mem_inf.mp d.b_mem_P).2
  have hρY : ∀ u ∈ d.Y3, rhoE h.J u ∈
      centralizer ({rhoE h.J d.z} : Set (MulAut (↥h.J ⧸ pPrimeCore 2 ↥h.J))) := by
    intro u hu
    have huN := hYN hu
    have h1 : u * (d.b * d.z) = d.b * d.z * u := mem_centralizer_singleton_iff.mp (mem_inf.mp hu).2
    have h2 : rhoE h.J (u * (d.b * d.z)) = rhoE h.J (d.b * d.z * u) := by rw [h1]
    rw [rhoE_mul huN (mul_mem hbN hzN), rhoE_mul (mul_mem hbN hzN) huN, rhoE_mul hbN hzN, hρb,
      one_mul] at h2
    exact mem_centralizer_singleton_iff.mpr h2
  have hyN := hYN hyY
  have hqY := hQY hq
  have hqN := hYN hqY
  set c := y * q * y⁻¹ * q⁻¹ with hcdef
  have hcQ : c ∈ Q := mul_mem (hyQ q hq) (inv_mem hq)
  have hcN : c ∈ normalizer (h.J : Set H) := hYN (hQY hcQ)
  obtain ⟨k, hk⟩ := hQ ⟨c, hcQ⟩
  have hck : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hρc : rhoE h.J c = rhoE h.J y * rhoE h.J q * (rhoE h.J y)⁻¹ * (rhoE h.J q)⁻¹ := by
    rw [hcdef, rhoE_mul (mul_mem (mul_mem hyN hqN) (inv_mem hyN)) (inv_mem hqN),
      rhoE_mul (mul_mem hyN hqN) (inv_mem hyN), rhoE_mul hyN hqN, rhoE_inv hyN, rhoE_inv hqN]
  have hρck : rhoE h.J c ^ 2 ^ k = 1 := by
    rw [rhoE_of_mem hcN, ← map_pow]
    have h1 : (⟨c, hcN⟩ : ↥(normalizer (h.J : Set H))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using hck)
    rw [h1, map_one]
  have hyo : Odd (orderOf (⟨rhoE h.J y, hρY y hyY⟩ :
      ↥(centralizer ({rhoE h.J d.z} : Set (MulAut (↥h.J ⧸ pPrimeCore 2 ↥h.J)))))) := by
    rw [Subgroup.orderOf_mk]
    have h1 : orderOf (rhoE h.J y) ∣ orderOf y := by
      rw [rhoE_of_mem hyN, ← Subgroup.orderOf_mk _ hyN]
      exact orderOf_map_dvd _ _
    exact Odd.of_dvd_nat ho h1
  have hxr := Three81.comm_of_hasNormalPComplement hΓ hyo
    (r := ⟨rhoE h.J q, hρY q hqY⟩) ⟨k, Subtype.ext (by
      simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
      rw [← hρc]
      exact hρck)⟩
  have hρc1 : rhoE h.J c = 1 := by
    have h1 : rhoE h.J y * rhoE h.J q = rhoE h.J q * rhoE h.J y := congrArg Subtype.val hxr
    rw [hρc, h1]
    group
  have hcK : c ∈ coreActionKernel h.J := (rhoE_eq_one_iff hcN).mp hρc1
  have hQ₀ : IsPGroup 2 ↥(Q ⊓ coreActionKernel h.J) := hQ.to_le inf_le_left
  have hQ₀le : Q ⊓ coreActionKernel h.J ≤ Y9 h ⊓ centralizer ({d.b * d.z} : Set H) := by
    intro w hw
    obtain ⟨hwQ, hwK⟩ := mem_inf.mp hw
    obtain ⟨hwa, hwbz⟩ := mem_inf.mp (hQY hwQ)
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨hwa, hwK⟩, hwbz⟩
  obtain ⟨e, -, hea, he⟩ := d.exists_four_of_le_kernel hQ₀ hQ₀le
  have hya : y * h.a = h.a * y := mem_centralizer_singleton_iff.mp (mem_inf.mp hyY).1
  have ha2 := h.orderOf_a
  have haa : h.a * h.a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have hcy : ∀ w ∈ Q ⊓ coreActionKernel h.J, y * w = w * y := by
    intro w hw
    have hw' : y * w * y⁻¹ ∈ Q ⊓ coreActionKernel h.J :=
      mem_inf.mpr ⟨hyQ w (mem_inf.mp hw).1,
        UnbalancedLayer.conj_mem_coreActionKernel hyN (mem_inf.mp hw).2⟩
    have hne := Three81.conj_ne_mul_of_odd (w := w) ho hya ha2
    have hfix : y * w * y⁻¹ = w := by
      have hfixa : y * h.a * y⁻¹ = h.a := by rw [hya]; group
      have hback : ∀ u : H, (u = 1 ∨ u = h.a) → y * w * y⁻¹ = u → y * w * y⁻¹ = w := by
        rintro u hu h1
        have h2 : w = u := by
          rcases hu with rfl | rfl
          · calc w = y⁻¹ * (y * w * y⁻¹) * y := by group
              _ = 1 := by rw [h1]; group
          · calc w = y⁻¹ * (y * w * y⁻¹) * y := by group
              _ = y⁻¹ * h.a * y := by rw [h1]
              _ = h.a := by rw [mul_assoc, ← hya, inv_mul_cancel_left]
        rw [h1, h2]
      rcases he _ hw' with h1 | h1 | h1 | h1
      · exact hback 1 (Or.inl rfl) h1
      · exact hback h.a (Or.inr rfl) h1
      · rcases he w hw with h2 | h2 | h2 | h2
        · rw [h2]; group
        · rw [h2, hfixa]
        · rw [h1, h2]
        · exfalso
          apply hne
          rw [h1, h2, ← mul_assoc, haa, one_mul]
      · rcases he w hw with h2 | h2 | h2 | h2
        · rw [h2]; group
        · rw [h2, hfixa]
        · exfalso
          apply hne
          rw [h1, h2]
        · rw [h1, h2]
    calc y * w = y * w * y⁻¹ * y := by group
      _ = w * y := by rw [hfix]
  exact Three81.comm_of_odd_of_comm_mem hQ₀ ho (mem_inf.mpr ⟨hcQ, hcK⟩) hcy

end Data

end L81Hyp

end Hyp59

theorem gs81Step3Input (hCent : CF81L2Cent2Nilp) : GS81Step3Input := by
  intro H _ _ h H₁ d _ _ _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  show HasNormalPComplement 2 ↥d.Y3
  rw [CFSG.GroupTheory.hasNormalPComplement_iff_isPGroup_automizer]
  intro Q hQ m
  induction m using QuotientGroup.induction_on with
  | H m =>
    obtain ⟨k, o, hodd, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m).ne'
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    have hyN : ((m ^ 2 ^ k : ↥(normalizer (Q : Set ↥d.Y3))) : ↥d.Y3) ∈
        normalizer (Q : Set ↥d.Y3) := (m ^ 2 ^ k).2
    have hyo : Odd (orderOf (((m ^ 2 ^ k : ↥(normalizer (Q : Set ↥d.Y3))) : ↥d.Y3) : H)) := by
      have h1 : orderOf (m ^ 2 ^ k) ∣ o :=
        orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, ← hord, pow_orderOf_eq_one])
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact Odd.of_dvd_nat hodd h1
    rw [mem_centralizer_iff]
    intro q hq
    have hQ' : IsPGroup 2 (Q.map d.Y3.subtype) := hQ.map _
    have hyQ : ∀ w ∈ Q.map d.Y3.subtype,
        (((m ^ 2 ^ k : ↥(normalizer (Q : Set ↥d.Y3))) : ↥d.Y3) : H) * w *
          (((m ^ 2 ^ k : ↥(normalizer (Q : Set ↥d.Y3))) : ↥d.Y3) : H)⁻¹ ∈
            Q.map d.Y3.subtype := by
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨_, (mem_normalizer_iff.mp hyN w).mp hw, rfl⟩
    have h1 := d.comm_of_odd_of_le_Y3 hCent hQ' (map_subtype_le _)
      (((m ^ 2 ^ k : ↥(normalizer (Q : Set ↥d.Y3))) : ↥d.Y3)).2 hyo hyQ ⟨q, hq, rfl⟩
    exact Subtype.ext h1.symm

end CFSG.ComponentClassification.GSThmB
