
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsEightsBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSylow
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsElem
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverAut
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryFixBase
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

structure IsQSetting {E : Type*} [Group E]
    (q : E →* Equiv.Perm (Fin 42)) (l : Cover →* E) : Prop where
  qS : ∀ e, q e ∈ S
  qsurj : ∀ s ∈ S, ∃ e, q e = s
  ker : q.ker = center E
  three : ∀ e ∈ q.ker, e ^ 3 = 1 → e = 1
  ql : q.comp l = sigma
  lsurj : Function.Surjective l

theorem cv_comm_of_commData {d : ℕ × ℕ × ℕ × ℕ × ℕ}
    (hd : d ∈ commData) (h0 : d.2.2 = (0, 0, 0)) :
    cv (tw d.1) * cv (tw d.2.1) = cv (tw d.2.1) * cv (tw d.1) := by
  have hs := comm_spec hd
  rw [h0] at hs
  simp only [pow_zero, mul_one] at hs
  calc cv (tw d.1) * cv (tw d.2.1) = cv (tw d.1) * cv (tw d.2.1) * (cv (tw d.1))⁻¹ *
      (cv (tw d.2.1))⁻¹ * (cv (tw d.2.1) * cv (tw d.1)) := by group
    _ = cv (tw d.2.1) * cv (tw d.1) := by rw [hs, one_mul]

theorem tg_mem_centralizer_T0
    {k : ℕ} (hk : k ∈ [0, 4, 8, 12]) :
    wordPerm (tg k) ∈ centralizer (T0 : Set (Equiv.Perm (Fin 42))) := by
  rw [mem_centralizer_iff]
  intro t ht
  exact mem_centralizer_singleton_iff.mp (T0_le_centralizer_tg hk ht)

theorem tg_not_mem_centralizer_T0
    {k : ℕ} (hk : k < 64) (hk' : k ∉ [0, 4, 8, 12]) :
    wordPerm (tg k) ∉ centralizer (T0 : Set (Equiv.Perm (Fin 42))) := by
  intro hc
  obtain ⟨k', hk'm, hkk⟩ := mem_center_T0 (tg_mem_T0 k hk)
    (fun t' ht' => ((mem_centralizer_iff.mp hc) t' ht').symm)
  have h64 : k' < 64 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk'm
    omega
  rw [tg_injective h64 hk hkk] at hk'm
  exact hk' hk'm

theorem not_mem_zpowers_tg {k j : ℕ} (hk : k < 64) (hj : j < 64)
    (hk0 : k ≠ 0) (hkj : k ≠ j) (hj2 : wordPerm (tg j) * wordPerm (tg j) = 1) :
    wordPerm (tg k) ∉ zpowers (wordPerm (tg j)) :=
  fun hmem => by
    rcases eq_one_or_eq_of_mem_zpowers hj2 hmem with h1 | h1
    · rw [← wordPerm_tg_zero] at h1
      exact hk0 (tg_injective hk (by norm_num) h1)
    · exact hkj (tg_injective hk hj h1)

namespace IsQSetting

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

theorem ker_le (h : IsQSetting q l) : q.ker ≤ center E :=
  h.ker ▸ le_refl _

theorem q_l (h : IsQSetting q l) (c : Cover) :
    q (l c) = sigma c := by
  rw [← MonoidHom.comp_apply, h.ql]

theorem q_lift (h : IsQSetting q l) {k : ℕ} (hk : k < 64) :
    q (l (cv (tw k))) = wordPerm (tg k) := by
  rw [h.q_l, sigma_tw k hk]

theorem psi_mem_ker
    (h : IsQSetting q l) (d) : psi l d ∈ q.ker := by
  have hz : zHom (((MonoidHom.id _).prodMap (MonoidHom.inl _ _)) d) ∈ sigma.ker :=
    range_zHom ▸ ⟨_, rfl⟩
  rw [MonoidHom.mem_ker, psi, MonoidHom.comp_apply, h.q_l]
  exact hz

theorem psi_comm
    (h : IsQSetting q l) (d) (g : E) :
    g * psi l d = psi l d * g :=
  mem_center_iff.mp (h.ker_le (h.psi_mem_ker d)) g

theorem lz₃
    (h : IsQSetting q l) : l z₃ = 1 :=
  lam_z₃ h.ql h.three

theorem q_ilift (h : IsQSetting q l) {d : ℕ × ℕ × ℕ × ℕ} (hd : d.1 < 64) :
    q (ilift l d) = wordPerm (tg d.1) := by
  rw [ilift, map_mul, h.q_lift hd, h.psi_mem_ker, mul_one]

theorem ilift_mul_self (h : IsQSetting q l) {d : ℕ × ℕ × ℕ × ℕ} (hd : d ∈ sqData) :
    ilift l d * ilift l d = 1 := by
  have hs := sq_spec hd
  have hsq : l (cv (tw d.1)) * l (cv (tw d.1)) = psi l (Multiplicative.ofAdd
      ((2 * d.2.1 : ℕ) : ZMod 4), Multiplicative.ofAdd ((2 * d.2.2.1 : ℕ) : ZMod 4)) := by
    rw [← map_mul, ← pow_two, hs, map_mul, map_mul, map_pow, map_pow, map_pow, h.lz₃, one_pow,
      mul_one, psi_ofAdd]
  have hc := h.psi_comm (Multiplicative.ofAdd (-(d.2.1 : ZMod 4)),
    Multiplicative.ofAdd (-(d.2.2.1 : ZMod 4))) (l (cv (tw d.1)))
  unfold ilift
  rw [← psi_sq_cancel l d.2.1 d.2.2.1, ← hsq]
  generalize l (cv (tw d.1)) = p at hc ⊢
  generalize psi l (Multiplicative.ofAdd (-(d.2.1 : ZMod 4)),
    Multiplicative.ofAdd (-(d.2.2.1 : ZMod 4))) = a at hc ⊢
  calc p * a * (p * a) = p * (a * p) * a := by group
    _ = p * (p * a) * a := by rw [hc]
    _ = p * p * (a * a) := by group

theorem ilift_comm (h : IsQSetting q l) {d d' : ℕ × ℕ × ℕ × ℕ}
    (hl : l (cv (tw d.1)) * l (cv (tw d'.1)) = l (cv (tw d'.1)) * l (cv (tw d.1))) :
    ilift l d * ilift l d' = ilift l d' * ilift l d := by
  unfold ilift
  have h1 := h.psi_comm (Multiplicative.ofAdd (-(d.2.1 : ZMod 4)),
    Multiplicative.ofAdd (-(d.2.2.1 : ZMod 4)))
  have h2 := h.psi_comm (Multiplicative.ofAdd (-(d'.2.1 : ZMod 4)),
    Multiplicative.ofAdd (-(d'.2.2.1 : ZMod 4)))
  generalize psi l (Multiplicative.ofAdd (-(d.2.1 : ZMod 4)),
    Multiplicative.ofAdd (-(d.2.2.1 : ZMod 4))) = a at h1 ⊢
  generalize psi l (Multiplicative.ofAdd (-(d'.2.1 : ZMod 4)),
    Multiplicative.ofAdd (-(d'.2.2.1 : ZMod 4))) = b at h2 ⊢
  generalize l (cv (tw d.1)) = x at hl ⊢
  generalize l (cv (tw d'.1)) = y at hl ⊢
  calc x * a * (y * b) = x * (a * y) * b := by group
    _ = x * (y * a) * b := by rw [h1]
    _ = x * y * (a * b) := by group
    _ = y * x * (a * b) := by rw [hl]
    _ = y * x * (b * a) := by rw [(h2 a).symm]
    _ = y * (x * b) * a := by group
    _ = y * (b * x) * a := by rw [h2]
    _ = y * b * (x * a) := by group

theorem exists_ker_involution (h : IsQSetting q l) (hne : q.ker ≠ ⊥) :
    ∃ ζ ∈ q.ker, ζ ≠ 1 ∧ ζ * ζ = 1 := by
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hne)
  have hz1' : z ≠ 1 := fun e => hz1 (Subtype.ext e)
  have h4 : z * z * (z * z) = 1 := by
    obtain ⟨i, j, rfl⟩ := (mem_ker_iff h.ql h.lsurj h.three).1 hz
    rw [← pow_four_eq, ← psi_ofAdd, ← map_pow]
    convert map_one (psi l) using 2
    refine Prod.ext ?_ ?_ <;> simp only [Prod.pow_fst, Prod.pow_snd, Prod.fst_one,
      Prod.snd_one] <;> rw [← ofAdd_nsmul, ← ofAdd_zero] <;> congr 1 <;>
      exact (by decide : ∀ x : ZMod 4, 4 • x = 0) _
  by_cases h2 : z * z = 1
  · exact ⟨z, hz, hz1', h2⟩
  · exact ⟨z * z, q.ker.mul_mem hz hz, h2, h4⟩

theorem tg_mul_self_of_ilift (h : IsQSetting q l) {d : ℕ × ℕ × ℕ × ℕ} (hd : d ∈ sqData)
    (h64 : d.1 < 64) : wordPerm (tg d.1) * wordPerm (tg d.1) = 1 := by
  rw [← h.q_ilift h64, ← map_mul, h.ilift_mul_self hd, map_one]

theorem exists_eights [Finite E]
    (h : IsQSetting q l) :
    ∃ E₁ E₂ : Subgroup E, E₁ ≤ U1.comap q ∧ E₂ ≤ U2.comap q ∧ IsEightGroup E₁ ∧
      IsEightGroup E₂ ∧ E₁ ≠ E₂ := by
  have hd1 : ((1, 0, 0, 2) : ℕ × ℕ × ℕ × ℕ) ∈ sqData := by decide
  have hd2 : ((2, 1, 0, 2) : ℕ × ℕ × ℕ × ℕ) ∈ sqData := by decide
  have hd4 : ((4, 1, 1, 1) : ℕ × ℕ × ℕ × ℕ) ∈ sqData := by decide
  have hd8 : ((8, 1, 0, 0) : ℕ × ℕ × ℕ × ℕ) ∈ sqData := by decide
  have hd16 : ((16, 1, 0, 2) : ℕ × ℕ × ℕ × ℕ) ∈ sqData := by decide
  have hq1 : q (ilift l (1, 0, 0, 2)) = wordPerm (tg 1) := h.q_ilift (by norm_num)
  have hq2 : q (ilift l (2, 1, 0, 2)) = wordPerm (tg 2) := h.q_ilift (by norm_num)
  have hq4 : q (ilift l (4, 1, 1, 1)) = wordPerm (tg 4) := h.q_ilift (by norm_num)
  have hq8 : q (ilift l (8, 1, 0, 0)) = wordPerm (tg 8) := h.q_ilift (by norm_num)
  have hq16 : q (ilift l (16, 1, 0, 2)) = wordPerm (tg 16) := h.q_ilift (by norm_num)
  have h1sq := h.ilift_mul_self hd1
  have h2sq := h.ilift_mul_self hd2
  have h4sq := h.ilift_mul_self hd4
  have h8sq := h.ilift_mul_self hd8
  have h16sq := h.ilift_mul_self hd16
  have ht1 := h.tg_mul_self_of_ilift hd1 (by norm_num)
  have ht4 := h.tg_mul_self_of_ilift hd4 (by norm_num)
  have hc48 : ilift l (4, 1, 1, 1) * ilift l (8, 1, 0, 0) =
      ilift l (8, 1, 0, 0) * ilift l (4, 1, 1, 1) :=
    h.ilift_comm (by
      rw [← map_mul, cv_comm_of_commData (d := (4, 8, 0, 0, 0)) (by decide) rfl, map_mul])
  have hc12 : ilift l (1, 0, 0, 2) * ilift l (2, 1, 0, 2) =
      ilift l (2, 1, 0, 2) * ilift l (1, 0, 0, 2) :=
    h.ilift_comm (by
      rw [← map_mul, cv_comm_of_commData (d := (1, 2, 0, 0, 0)) (by decide) rfl, map_mul])
  have hne1 : ∀ x : E, q x = wordPerm (tg 1) → x ≠ 1 := fun x hx h1 => by
    rw [h1, map_one, ← wordPerm_tg_zero] at hx
    exact absurd (tg_injective (by norm_num) (by norm_num) hx) (by norm_num)
  have hne4 : ∀ x : E, q x = wordPerm (tg 4) → x ≠ 1 := fun x hx h1 => by
    rw [h1, map_one, ← wordPerm_tg_zero] at hx
    exact absurd (tg_injective (by norm_num) (by norm_num) hx) (by norm_num)
  have hcen : ∀ {a b : E}, q a ∈ centralizer (T0 : Set (Equiv.Perm (Fin 42))) →
      q b ∈ centralizer (T0 : Set (Equiv.Perm (Fin 42))) →
      zpowers b ⊔ zpowers a ≤ (centralizer (T0 : Set (Equiv.Perm (Fin 42)))).comap q :=
    fun ha hb => sup_le (zpowers_le.2 hb) (zpowers_le.2 ha)
  have hc4 : q (ilift l (4, 1, 1, 1)) ∈ centralizer (T0 : Set (Equiv.Perm (Fin 42))) := by
    rw [hq4]; exact tg_mem_centralizer_T0 (by decide)
  have hc8 : q (ilift l (8, 1, 0, 0)) ∈ centralizer (T0 : Set (Equiv.Perm (Fin 42))) := by
    rw [hq8]; exact tg_mem_centralizer_T0 (by decide)
  have hn1 : q (ilift l (1, 0, 0, 2)) ∉ centralizer (T0 : Set (Equiv.Perm (Fin 42))) := by
    rw [hq1]; exact tg_not_mem_centralizer_T0 (by norm_num) (by decide)
  have hn16 : q (ilift l (16, 1, 0, 2)) ∉ centralizer (T0 : Set (Equiv.Perm (Fin 42))) := by
    rw [hq16]; exact tg_not_mem_centralizer_T0 (by norm_num) (by decide)
  have hn84 : ilift l (8, 1, 0, 0) ∉ zpowers (ilift l (4, 1, 1, 1)) := fun hmem => by
    have := map_mem_zpowers q hmem
    rw [hq8, hq4] at this
    exact not_mem_zpowers_tg (by norm_num) (by norm_num) (by norm_num) (by norm_num) ht4 this
  have hU1 : ∀ {k : ℕ}, k < 16 → ∀ {x : E}, q x = wordPerm (tg k) → x ∈ U1.comap q :=
    fun hk x hx => by rw [mem_comap, hx]; exact tg_mem_U1 hk
  have hU2 : ∀ {k : ℕ}, k < 16 → ∀ {x : E}, q x = wordPerm (tg (4 * k)) → x ∈ U2.comap q :=
    fun hk x hx => by rw [mem_comap, hx]; exact tg_mem_U2 hk
  have hn1U2 : q (ilift l (1, 0, 0, 2)) ∉ U2 := by
    rw [hq1, mem_U2_iff]
    rintro ⟨k, hk, hkt⟩
    have := tg_injective (by omega) (by norm_num) hkt
    omega
  by_cases hk : q.ker = ⊥
  · have hinj : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).1 hk
    have hcomm : ∀ {a b : E}, q b ∈ centralizer (T0 : Set (Equiv.Perm (Fin 42))) →
        q a ∈ T0 → a * b = b * a := fun hb ha =>
      hinj (by rw [map_mul, map_mul]; exact (mem_centralizer_iff.mp hb) _ ha)
    have hT : ∀ {x : E} {k : ℕ}, k < 64 → q x = wordPerm (tg k) → q x ∈ T0 :=
      fun hk64 hx => hx ▸ tg_mem_T0 _ hk64
    refine ⟨zpowers (ilift l (1, 0, 0, 2)) ⊔ (zpowers (ilift l (8, 1, 0, 0)) ⊔
        zpowers (ilift l (4, 1, 1, 1))), zpowers (ilift l (16, 1, 0, 2)) ⊔
        (zpowers (ilift l (8, 1, 0, 0)) ⊔ zpowers (ilift l (4, 1, 1, 1))), ?_, ?_, ?_, ?_, ?_⟩
    · exact sup_le (zpowers_le.2 (hU1 (by norm_num) hq1))
        (sup_le (zpowers_le.2 (hU1 (by norm_num) hq8)) (zpowers_le.2 (hU1 (by norm_num) hq4)))
    · exact sup_le (zpowers_le.2 (hU2 (k := 4) (by norm_num) hq16))
        (sup_le (zpowers_le.2 (hU2 (k := 2) (by norm_num) hq8))
          (zpowers_le.2 (hU2 (k := 1) (by norm_num) hq4)))
    · exact isEightGroup_of_three h4sq h8sq h1sq hc48
        (hcomm hc4 (hT (by norm_num) hq1)).symm (hcomm hc8 (hT (by norm_num) hq1)).symm
        (hne4 _ hq4) hn84 (not_mem_of_le_comap (hcen hc4 hc8) hn1)
    · exact isEightGroup_of_three h4sq h8sq h16sq hc48
        (hcomm hc4 (hT (by norm_num) hq16)).symm (hcomm hc8 (hT (by norm_num) hq16)).symm
        (hne4 _ hq4) hn84 (not_mem_of_le_comap (hcen hc4 hc8) hn16)
    · intro heq
      have hmem : ilift l (1, 0, 0, 2) ∈ zpowers (ilift l (16, 1, 0, 2)) ⊔
          (zpowers (ilift l (8, 1, 0, 0)) ⊔ zpowers (ilift l (4, 1, 1, 1))) :=
        heq ▸ mem_sup_left (mem_zpowers _)
      have hle : zpowers (ilift l (16, 1, 0, 2)) ⊔ (zpowers (ilift l (8, 1, 0, 0)) ⊔
          zpowers (ilift l (4, 1, 1, 1))) ≤ U2.comap q :=
        sup_le (zpowers_le.2 (hU2 (k := 4) (by norm_num) hq16))
          (sup_le (zpowers_le.2 (hU2 (k := 2) (by norm_num) hq8))
            (zpowers_le.2 (hU2 (k := 1) (by norm_num) hq4)))
      exact hn1U2 (hle hmem)
  · obtain ⟨ζ, hζk, hζ1, hζ2⟩ := h.exists_ker_involution hk
    have hζc : ∀ x : E, ζ * x = x * ζ := fun x => (mem_center_iff.mp (h.ker_le hζk) x).symm
    have hζq : q ζ = 1 := hζk
    refine ⟨zpowers (ilift l (2, 1, 0, 2)) ⊔ (zpowers (ilift l (1, 0, 0, 2)) ⊔ zpowers ζ),
      zpowers (ilift l (8, 1, 0, 0)) ⊔ (zpowers (ilift l (4, 1, 1, 1)) ⊔ zpowers ζ),
      ?_, ?_, ?_, ?_, ?_⟩
    · refine sup_le (zpowers_le.2 (hU1 (by norm_num) hq2))
        (sup_le (zpowers_le.2 (hU1 (by norm_num) hq1)) (zpowers_le.2 ?_))
      rw [mem_comap, hζq]
      exact U1.one_mem
    · refine sup_le (zpowers_le.2 (hU2 (k := 2) (by norm_num) hq8))
        (sup_le (zpowers_le.2 (hU2 (k := 1) (by norm_num) hq4)) (zpowers_le.2 ?_))
      rw [mem_comap, hζq]
      exact U2.one_mem
    · refine isEightGroup_of_three hζ2 h1sq h2sq (hζc _) (hζc _) hc12 hζ1 ?_ ?_
      · intro hmem
        have := map_mem_zpowers q hmem
        rw [hq1, hζq, zpowers_one_eq_bot, mem_bot, ← wordPerm_tg_zero] at this
        exact absurd (tg_injective (by norm_num) (by norm_num) this) (by norm_num)
      · intro hmem
        have hle : zpowers (ilift l (1, 0, 0, 2)) ⊔ zpowers ζ ≤
            (zpowers (wordPerm (tg 1))).comap q :=
          sup_le (zpowers_le.2 (by rw [mem_comap, hq1]; exact mem_zpowers _))
            (zpowers_le.2 (by rw [mem_comap, hζq]; exact one_mem _))
        have := hle hmem
        rw [mem_comap, hq2] at this
        exact not_mem_zpowers_tg (by norm_num) (by norm_num) (by norm_num) (by norm_num) ht1 this
    · refine isEightGroup_of_three hζ2 h4sq h8sq (hζc _) (hζc _) hc48 hζ1 ?_ ?_
      · intro hmem
        have := map_mem_zpowers q hmem
        rw [hq4, hζq, zpowers_one_eq_bot, mem_bot, ← wordPerm_tg_zero] at this
        exact absurd (tg_injective (by norm_num) (by norm_num) this) (by norm_num)
      · intro hmem
        have hle : zpowers (ilift l (4, 1, 1, 1)) ⊔ zpowers ζ ≤
            (zpowers (wordPerm (tg 4))).comap q :=
          sup_le (zpowers_le.2 (by rw [mem_comap, hq4]; exact mem_zpowers _))
            (zpowers_le.2 (by rw [mem_comap, hζq]; exact one_mem _))
        have := hle hmem
        rw [mem_comap, hq8] at this
        exact not_mem_zpowers_tg (by norm_num) (by norm_num) (by norm_num) (by norm_num) ht4 this
    · intro heq
      have hmem : ilift l (1, 0, 0, 2) ∈ zpowers (ilift l (8, 1, 0, 0)) ⊔
          (zpowers (ilift l (4, 1, 1, 1)) ⊔ zpowers ζ) :=
        heq ▸ mem_sup_right (mem_sup_left (mem_zpowers _))
      have hle : zpowers (ilift l (8, 1, 0, 0)) ⊔ (zpowers (ilift l (4, 1, 1, 1)) ⊔ zpowers ζ) ≤
          (centralizer (T0 : Set (Equiv.Perm (Fin 42)))).comap q :=
        sup_le (zpowers_le.2 hc8) (sup_le (zpowers_le.2 hc4) (zpowers_le.2 (by
          rw [mem_comap, hζq]; exact one_mem _)))
      exact hn1 (hle hmem)

end IsQSetting

end CFSG.ComponentClassification.GrSLit.L34Facts
