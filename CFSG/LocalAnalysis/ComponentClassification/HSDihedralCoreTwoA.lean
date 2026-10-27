module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwo
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTbar

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup

variable {X : Type} [Group X] [Finite X] {A : Type} [Group A]

namespace LocalDatum

variable {Δ : LocalDatum X A} {k : A} (h2 : Δ.CaseTwo k) (φ : Δ.Fusion)

include h2 in
theorem TwoA_conj_dz (hu : ∃ u ∈ Δ.D, u ≠ 1 ∧ φ.x⁻¹ * u * φ.x ∈ Δ.D) :
    φ.x * Δ.dz * φ.x⁻¹ = Δ.dz := by
  have h8 := h2.2.2.2.2.1
  set N := Δ.D ⊓ Δ.D.map (MulAut.conj φ.x).toMonoidHom
  have hNS : N ≤ Δ.S := inf_le_left.trans Δ.D_le
  have hN : ∀ s ∈ Δ.S, ∀ n ∈ N, s * n * s⁻¹ ∈ N := by
    intro s hs n hn
    obtain ⟨hnD, hnD'⟩ := mem_inf.mp hn
    rw [mem_map_conj_iff] at hnD'
    refine mem_inf.mpr ⟨Δ.conj_mem_D s hs n hnD, mem_map_conj_iff.mpr ?_⟩
    have h := Δ.conj_mem_D _ (φ.conj_inv_mem hs) _ hnD'
    have he : φ.x⁻¹ * (s * n * s⁻¹) * φ.x =
        φ.x⁻¹ * s * φ.x * (φ.x⁻¹ * n * φ.x) * (φ.x⁻¹ * s * φ.x)⁻¹ := by group
    rw [he]
    exact h
  obtain ⟨u, hu, hu1, hu'⟩ := hu
  obtain ⟨v, hvN, hv1, -, hvc⟩ := exists_central_inv_of_normal Δ.sylow.isPGroup hNS hN
    ⟨u, mem_inf.mpr ⟨hu, mem_map_conj_iff.mpr hu'⟩, hu1⟩
  obtain ⟨hvD, hvD'⟩ := mem_inf.mp hvN
  rw [mem_map_conj_iff] at hvD'
  have hv : v = Δ.dz :=
    (Δ.eq_dz_of_central h8 hvD fun d hd => (hvc d (Δ.D_le hd)).symm).resolve_left hv1
  have hv' : φ.x⁻¹ * v * φ.x = Δ.dz := by
    refine (Δ.eq_dz_of_central h8 hvD' fun d hd => ?_).resolve_left ?_
    · have h := hvc _ (φ.conj_mem d (Δ.D_le hd))
      calc φ.x⁻¹ * v * φ.x * d = φ.x⁻¹ * (v * (φ.x * d * φ.x⁻¹)) * φ.x := by group
        _ = φ.x⁻¹ * ((φ.x * d * φ.x⁻¹) * v) * φ.x := by rw [← h]
        _ = d * (φ.x⁻¹ * v * φ.x) := by group
    · intro h
      apply hv1
      calc v = φ.x * (φ.x⁻¹ * v * φ.x) * φ.x⁻¹ := by group
        _ = 1 := by rw [h]; group
  rw [hv] at hv'
  calc φ.x * Δ.dz * φ.x⁻¹ = φ.x * (φ.x⁻¹ * Δ.dz * φ.x) * φ.x⁻¹ := by rw [hv']
    _ = Δ.dz := by group

include h2 in
theorem TwoA_commute (hxz : φ.x * Δ.dz * φ.x⁻¹ = Δ.dz) {q : X} (hq : q ∈ Δ.Q) {d : X}
    (hd : d ∈ Δ.D) : φ.x * q * φ.x⁻¹ * d = d * (φ.x * q * φ.x⁻¹) := by
  have h8 := h2.2.2.2.2.1
  have hqS : φ.x * q * φ.x⁻¹ ∈ Δ.S := φ.conj_mem q (Δ.Q_le hq)
  set c := φ.x * q * φ.x⁻¹ * d * (φ.x * q * φ.x⁻¹)⁻¹ * d⁻¹
  have hcD : c ∈ Δ.D := mul_mem (Δ.conj_mem_D _ hqS d hd) (inv_mem hd)
  have hcQ : φ.x⁻¹ * c * φ.x ∈ Δ.Q := by
    have he : φ.x⁻¹ * c * φ.x =
        q * ((φ.x⁻¹ * d * φ.x) * q⁻¹ * (φ.x⁻¹ * d * φ.x)⁻¹) := by simp only [c]; group
    rw [he]
    exact mul_mem hq (Δ.conj_mem_Q (φ.conj_inv_mem (Δ.D_le hd)) (inv_mem hq))
  by_contra hne
  have hc1 : c ≠ 1 := fun h => hne (by
    calc φ.x * q * φ.x⁻¹ * d = c * (d * (φ.x * q * φ.x⁻¹)) := by simp only [c]; group
      _ = d * (φ.x * q * φ.x⁻¹) := by rw [h, one_mul])
  set N := Δ.D ⊓ Δ.Q.map (MulAut.conj φ.x).toMonoidHom
  have hz : Δ.dz ∈ N := by
    refine Δ.dz_mem_of_normal h8 inf_le_left (fun h => hc1 ?_) fun d' hd' n hn => ?_
    · have : c ∈ N := mem_inf.mpr ⟨hcD, mem_map_conj_iff.mpr hcQ⟩
      rw [h] at this
      exact mem_bot.mp this
    · obtain ⟨hnD, hnQ⟩ := mem_inf.mp hn
      rw [mem_map_conj_iff] at hnQ
      refine mem_inf.mpr ⟨Δ.conj_mem_D d' (Δ.D_le hd') n hnD, mem_map_conj_iff.mpr ?_⟩
      have he : φ.x⁻¹ * (d' * n * d'⁻¹) * φ.x =
          φ.x⁻¹ * d' * φ.x * (φ.x⁻¹ * n * φ.x) * (φ.x⁻¹ * d' * φ.x)⁻¹ := by group
      rw [he]
      exact Δ.conj_mem_Q (φ.conj_inv_mem (Δ.D_le hd')) hnQ
  have hzQ : Δ.dz ∈ Δ.Q := by
    have h := mem_map_conj_iff.mp (mem_inf.mp hz).2
    have he : φ.x⁻¹ * Δ.dz * φ.x = Δ.dz := by
      calc φ.x⁻¹ * Δ.dz * φ.x = φ.x⁻¹ * (φ.x * Δ.dz * φ.x⁻¹) * φ.x := by rw [hxz]
        _ = Δ.dz := by group
    rwa [he] at h
  exact Δ.dz_ne_one (Δ.eq_one_of_mem_Q_D hzQ Δ.dz_mem)

include h2 in
theorem TwoA_Q (hxQ : ∀ q ∈ Δ.Q, ∀ d ∈ Δ.D, φ.x * q * φ.x⁻¹ * d = d * (φ.x * q * φ.x⁻¹)) :
    ∀ q ∈ Δ.Q, q = 1 ∨ q = Δ.t := by
  intro y hy
  by_contra hne
  push Not at hne
  obtain ⟨q, hq, hqt⟩ := Δ.exists_sq_eq_t hy hne.1 hne.2
  have h := Δ.sq_mem_Q_of_caseTwo h2 (φ.conj_mem q (Δ.Q_le hq)) (hxQ q hq)
  have he : (φ.x * q * φ.x⁻¹) ^ 2 = φ.x * Δ.t * φ.x⁻¹ := by
    rw [← hqt, pow_two, pow_two]
    group
  rw [he] at h
  exact φ.conj_t_ne (Δ.eq_t_of_mem_Q h φ.conj_t_sq φ.conj_t_ne_one)

include h2 in
theorem TwoA_c (hQ : ∀ q ∈ Δ.Q, q = 1 ∨ q = Δ.t) {c : X} (hcS : c ∈ Δ.S)
    (hcD : ∀ d ∈ Δ.D, c * d = d * c) (hct : c ^ 2 = Δ.t) : Δ.ψe c * k ∈ Δ.Dbar := by
  rcases h2.2.2.2.2.2 _ (Δ.ψe_mem_R hcS) (Δ.commute_Dbar hcS hcD) with h | h
  · exfalso
    obtain ⟨q, hq, hcq⟩ := Δ.mem_Qz_of_centralizes h2.2.2.2.2.1 hcS hcD h
    have hq2 : q ^ 2 = 1 := by
      rcases hQ q hq with rfl | rfl
      · exact one_pow 2
      · exact Δ.t_sq
    have hqz : q * Δ.dz = Δ.dz * q := Δ.commute_of_mem_Q_D hq Δ.dz_mem
    have : c ^ 2 = 1 := by
      rcases hcq with rfl | rfl
      · exact hq2
      · rw [(show Commute q Δ.dz from hqz).mul_pow, hq2, Δ.dz_sq, one_mul]
    rw [hct] at this
    exact Δ.t_ne_one this
  · exact h

include h2 in
theorem TwoA_no_inv (hQ : ∀ q ∈ Δ.Q, q = 1 ∨ q = Δ.t) {c : X} (hcS : c ∈ Δ.S)
    (hcD : ∀ d ∈ Δ.D, c * d = d * c) (hct : c ^ 2 = Δ.t) {s : X} (hs : s ∈ Δ.S)
    (hs2 : s ^ 2 = 1) (hsk : Δ.ψe s * k ∈ Δ.Dbar) : False := by
  have hck := TwoA_c h2 hQ hcS hcD hct
  have hD : Δ.ψe (s * c⁻¹) ∈ Δ.Dbar := by
    rw [Δ.ψe_mul hs (inv_mem hcS), Δ.ψe_inv hcS]
    have := mul_mem hsk (inv_mem hck)
    simpa [mul_assoc] using this
  obtain ⟨q, hq, d, hd, hqd⟩ := Δ.exists_QD (mul_mem hs (inv_mem hcS)) hD
  have hseq : s = q * d * c := by rw [← hqd]; group
  have hqc : ∀ y ∈ Δ.S, q * y = y * q := fun y hy => by
    rcases hQ q hq with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (Δ.commute_t hy).symm
  have hdc : d * c = c * d := (hcD d hd).symm
  have hq2 : q ^ 2 = 1 := by
    rcases hQ q hq with rfl | rfl
    · exact one_pow 2
    · exact Δ.t_sq
  have hs2' : s ^ 2 = d ^ 2 * Δ.t := by
    rw [hseq, mul_assoc, (show Commute q (d * c) from hqc _ (mul_mem (Δ.D_le hd) hcS)).mul_pow,
      hq2, one_mul, (show Commute d c from hdc).mul_pow, hct]
  rw [hs2] at hs2'
  apply Δ.t_not_mem_D
  have : Δ.t = (d ^ 2)⁻¹ := by
    calc Δ.t = (d ^ 2)⁻¹ * (d ^ 2 * Δ.t) := by group
      _ = (d ^ 2)⁻¹ := by rw [← hs2', mul_one]
  rw [this]
  exact inv_mem (pow_mem hd 2)

include h2 in
theorem TwoA_conj_t (hxz : φ.x * Δ.dz * φ.x⁻¹ = Δ.dz)
    (hxQ : ∀ q ∈ Δ.Q, ∀ d ∈ Δ.D, φ.x * q * φ.x⁻¹ * d = d * (φ.x * q * φ.x⁻¹))
    (hQ : ∀ q ∈ Δ.Q, q = 1 ∨ q = Δ.t) {c : X} (hcS : c ∈ Δ.S)
    (hcD : ∀ d ∈ Δ.D, c * d = d * c) (hct : c ^ 2 = Δ.t) :
    φ.x * Δ.t * φ.x⁻¹ = Δ.t * Δ.dz := by
  have htS := φ.conj_t_mem
  have htD := hxQ _ Δ.t_mem_Q
  rcases h2.2.2.2.2.2 _ (Δ.ψe_mem_R htS) (Δ.commute_Dbar htS htD) with h | h
  · obtain ⟨q, hq, hcq⟩ := Δ.mem_Qz_of_centralizes h2.2.2.2.2.1 htS htD h
    rcases hcq with h' | h'
    · rcases hQ q hq with rfl | rfl
      · exact absurd h' φ.conj_t_ne_one
      · exact absurd h' φ.conj_t_ne
    · rcases hQ q hq with rfl | rfl
      · exfalso
        rw [one_mul, ← hxz] at h'
        have : Δ.t = Δ.dz := by
          have := congrArg (fun y => φ.x⁻¹ * y * φ.x) h'
          simpa [mul_assoc] using this
        exact Δ.t_not_mem_D (this ▸ Δ.dz_mem)
      · exact h'
  · exact (TwoA_no_inv h2 hQ hcS hcD hct htS φ.conj_t_sq h).elim

include h2 φ in
theorem TwoA_false_of_inv (hQ : ∀ q ∈ Δ.Q, q = 1 ∨ q = Δ.t) {c : X} (hcS : c ∈ Δ.S)
    (hcD : ∀ d ∈ Δ.D, c * d = d * c) (hct : c ^ 2 = Δ.t)
    (hinv : ∀ i ∈ Δ.S, i ^ 2 = 1 → Δ.ψe i ∈ Δ.Dbar) : False := by
  refine φ.false_of_char_inv (fun c' hc' hc'I => Δ.sq_mem_Q_of_caseTwo h2 hc' fun d hd =>
    Δ.commute_of_commute_inv (fun i hi hi2 => hc'I i (Δ.D_le hi) hi2) hd) hcS
    (fun i hi hi2 => ?_) hct
  obtain ⟨q, hq, d, hd, rfl⟩ := Δ.exists_QD hi (hinv i hi hi2)
  have hcq : c * q = q * c := by
    rcases hQ q hq with rfl | rfl
    · rw [one_mul, mul_one]
    · exact Δ.commute_t hcS
  calc c * (q * d) = q * (c * d) := by rw [← mul_assoc, hcq, mul_assoc]
    _ = q * d * c := by rw [hcD d hd, mul_assoc]

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
