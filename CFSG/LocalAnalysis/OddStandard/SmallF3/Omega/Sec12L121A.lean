module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L120A

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S E : Subgroup G}

private theorem sec121_f_inv (F : Sec12Frame t L S) {p : G} (hp : p ∈ secCMB t S L) :
    sec12f t p⁻¹ = (sec12f t p)⁻¹ := by
  have hp1 : p⁻¹ ∈ secCMB t S L := (secCMB t S L).inv_mem hp
  have h1 : sec12f t p * sec12f t p⁻¹ = 1 := by
    have hmul := sec12E_f_mul F hp hp1
    rw [mul_inv_cancel] at hmul
    simpa [sec12f] using hmul.symm
  exact eq_inv_of_mul_eq_one_right h1

private theorem sec121_conj_mem_V (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    {a x : G} (ha : a ∈ E) (hx : x ∈ secV t S L E) : a * x * a⁻¹ ∈ secV t S L E := by
  have hle : secV t S L E ≤ (secV t S L E).comap (MulAut.conj a).toMonoidHom := by
    rw [secV, Subgroup.commutator_le]
    intro e he y hy
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hid : a * ⁅e, y⁆ * a⁻¹ = ⁅a * e, y⁆ * ⁅a, y⁆⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
      group
    rw [hid]
    exact (secV t S L E).mul_mem
      (Subgroup.commutator_mem_commutator (E.mul_mem ha he) hy)
      ((secV t S L E).inv_mem (Subgroup.commutator_mem_commutator ha hy))
  have h := Subgroup.mem_comap.mp (hle hx)
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

private theorem sec121_conj_mem_V_Y (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    {b x : G} (hb : b ∈ secM t S L ⊓ L) (hx : x ∈ secV t S L E) :
    b * x * b⁻¹ ∈ secV t S L E := by
  have hbE := sec12E_sylow_normal F hE hb.1
  have hle : secV t S L E ≤ (secV t S L E).comap (MulAut.conj b).toMonoidHom := by
    rw [secV, Subgroup.commutator_le]
    intro e he y hy
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hid : b * ⁅e, y⁆ * b⁻¹ = ⁅b * e * b⁻¹, b * y * b⁻¹⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [hid]
    exact Subgroup.commutator_mem_commutator
      ((Subgroup.mem_normalizer_iff.mp hbE e).mp he)
      ((secM t S L ⊓ L).mul_mem ((secM t S L ⊓ L).mul_mem hb hy) ((secM t S L ⊓ L).inv_mem hb))
  have h := Subgroup.mem_comap.mp (hle hx)
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

theorem sec121_V_le_E (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L)) :
    secV t S L E ≤ E := by
  rw [secV, Subgroup.commutator_le]
  intro e he y hy
  have hconj : y * e⁻¹ * y⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (sec12E_sylow_normal F hE hy.1) e⁻¹).mp (E.inv_mem he)
  have heq : ⁅e, y⁆ = e * (y * e⁻¹ * y⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [heq]
  exact E.mul_mem he hconj

theorem sec121_E_le_normalizer_V (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L)) :
    E ≤ normalizer (secV t S L E : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => sec121_conj_mem_V F hE ha hx, fun hx => ?_⟩
  have h := sec121_conj_mem_V F hE (E.inv_mem ha) hx
  have hx' : a⁻¹ * (a * x * a⁻¹) * (a⁻¹)⁻¹ = x := by group
  rwa [hx'] at h

theorem sec121_Y_le_normalizer_V (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L)) :
    secM t S L ⊓ L ≤ normalizer (secV t S L E : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => sec121_conj_mem_V_Y F hE hb hx, fun hx => ?_⟩
  have h := sec121_conj_mem_V_Y F hE ((secM t S L ⊓ L).inv_mem hb) hx
  have hx' : b⁻¹ * (b * x * b⁻¹) * (b⁻¹)⁻¹ = x := by group
  rwa [hx'] at h

theorem sec121_B_le_V (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L)) :
    secB S L ≤ secV t S L E := by
  have hBE : secB S L ≤ E := le_sup_left.trans (sec120_A_le_E F hE)
  have hmono : ⁅secM t S L ⊓ L, secB S L⁆ ≤ ⁅secM t S L ⊓ L, E⁆ :=
    Subgroup.commutator_mono le_rfl hBE
  have heq : ⁅secM t S L ⊓ L, E⁆ = secV t S L E := by
    rw [secV]
    exact Subgroup.commutator_comm (secM t S L ⊓ L) E
  exact (sec12E_B_le_comm F).trans (hmono.trans heq.le)

theorem sec121_f_surj_V (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L)) {b : G}
    (hb : b ∈ secB S L) : ∃ v ∈ secV t S L E, sec12f t v = b := by
  have hVE : secV t S L E ≤ E := sec121_V_le_E F hE
  have hVP : secV t S L E ≤ secCMB t S L := hVE.trans hE.1
  let Ψ : Subgroup G :=
    { carrier := {x : G | ∃ v ∈ secV t S L E, sec12f t v = x}
      one_mem' := ⟨1, (secV t S L E).one_mem, by simp [sec12f]⟩
      mul_mem' := by
        rintro x y ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
        exact ⟨v * w, (secV t S L E).mul_mem hv hw, sec12E_f_mul F (hVP hv) (hVP hw)⟩
      inv_mem' := by
        rintro x ⟨v, hv, rfl⟩
        exact ⟨v⁻¹, (secV t S L E).inv_mem hv, sec121_f_inv F (hVP hv)⟩ }
  have hgen : ∀ y ∈ secM t S L ⊓ L, ∀ b' ∈ secB S L, ⁅y, b'⁆ ∈ Ψ := by
    intro y hy b' hb'
    obtain ⟨e, he, hfe⟩ := sec120_f_surj_E F hE hb'
    have hyE : y * e * y⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (sec12E_sylow_normal F hE hy.1) e).mp he
    have hyP : y * e * y⁻¹ ∈ secCMB t S L := hE.1 hyE
    have heiP : e⁻¹ ∈ secCMB t S L := (secCMB t S L).inv_mem (hE.1 he)
    have hvV : y * e * y⁻¹ * e⁻¹ ∈ secV t S L E := by
      have h1 : ⁅e, y⁆ ∈ secV t S L E := Subgroup.commutator_mem_commutator he hy
      have h2 : y * e * y⁻¹ * e⁻¹ = ⁅e, y⁆⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [h2]
      exact (secV t S L E).inv_mem h1
    refine ⟨y * e * y⁻¹ * e⁻¹, hvV, ?_⟩
    have hyt : y * t = t * y := (Subgroup.mem_centralizer_iff.mp F.htC) y hy.2
    calc sec12f t (y * e * y⁻¹ * e⁻¹)
        = sec12f t (y * e * y⁻¹) * sec12f t e⁻¹ := sec12E_f_mul F hyP heiP
      _ = (y * sec12f t e * y⁻¹) * (sec12f t e)⁻¹ := by
            rw [sec12E_f_conj hyt e, sec121_f_inv F (hE.1 he)]
      _ = ⁅y, b'⁆ := by rw [hfe, commutatorElement_def]
  have hle : ⁅secM t S L ⊓ L, secB S L⁆ ≤ Ψ := Subgroup.commutator_le.mpr hgen
  have hbΨ : b ∈ Ψ := hle (sec12E_B_le_comm F hb)
  obtain ⟨v, hv, hfv⟩ := hbΨ
  exact ⟨v, hv, hfv⟩

theorem sec121_comm_A_Y (F : Sec12Frame t L S) {a y : G} (ha : a ∈ secA t S L)
    (hy : y ∈ secM t S L ⊓ L) : a * y * a⁻¹ * y⁻¹ ∈ secB S L := by
  rcases (sec12E_mem_A F).mp ha with haB | ⟨b₀, hb₀, rfl⟩
  · have h1 : y * a⁻¹ * y⁻¹ ∈ secB S L :=
      F.normB y hy.1 a⁻¹ ((secB S L).inv_mem haB)
    have h2 : a * (y * a⁻¹ * y⁻¹) ∈ secB S L := (secB S L).mul_mem haB h1
    have heq : a * y * a⁻¹ * y⁻¹ = a * (y * a⁻¹ * y⁻¹) := by group
    rwa [heq]
  · have hc : b₀ * (y * b₀⁻¹ * y⁻¹) ∈ secB S L :=
      (secB S L).mul_mem hb₀ (F.normB y hy.1 b₀⁻¹ ((secB S L).inv_mem hb₀))
    have hct : t * (b₀ * (y * b₀⁻¹ * y⁻¹)) = (b₀ * (y * b₀⁻¹ * y⁻¹)) * t :=
      sec12E_t_comm_B F hc
    have hyt : y * t = t * y := (Subgroup.mem_centralizer_iff.mp F.htC) y hy.2
    have hytinv : t⁻¹ * y⁻¹ = y⁻¹ * t⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, hyt]
    have heq : (t * b₀) * y * (t * b₀)⁻¹ * y⁻¹
        = t * (b₀ * (y * b₀⁻¹ * y⁻¹)) * t⁻¹ := by
      have e1 : (t * b₀) * y * (t * b₀)⁻¹ * y⁻¹
          = t * (b₀ * y * b₀⁻¹) * (t⁻¹ * y⁻¹) := by group
      rw [e1, hytinv]
      group
    have htct : t * (b₀ * (y * b₀⁻¹ * y⁻¹)) * t⁻¹ = b₀ * (y * b₀⁻¹ * y⁻¹) := by
      rw [hct]
      group
    rw [heq, htct]
    exact hc

theorem sec121_V_le_V0 (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    {V0 : Subgroup G} (hB : secB S L ≤ V0)
    (hinv : ∀ y ∈ secM t S L ⊓ L, ∀ x ∈ V0, y * x * y⁻¹ ∈ V0)
    (hdec : ∀ e ∈ E, ∃ x ∈ V0, ∃ a ∈ secA t S L, e = x * a) : secV t S L E ≤ V0 := by
  rw [secV, Subgroup.commutator_le]
  intro e he y hy
  obtain ⟨x, hx, a, ha, rfl⟩ := hdec e he
  have h1 : ⁅a, y⁆ ∈ V0 := by
    rw [commutatorElement_def]
    exact hB (sec121_comm_A_Y F ha hy)
  have h2 : x * ⁅a, y⁆ * x⁻¹ ∈ V0 := V0.mul_mem (V0.mul_mem hx h1) (V0.inv_mem hx)
  have h3 : ⁅x, y⁆ ∈ V0 := by
    have hyx : y * x⁻¹ * y⁻¹ ∈ V0 := hinv y hy x⁻¹ (V0.inv_mem hx)
    have heq : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact V0.mul_mem hx hyx
  have hid : ⁅x * a, y⁆ = x * ⁅a, y⁆ * x⁻¹ * ⁅x, y⁆ := by
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
    group
  rw [hid]
  exact V0.mul_mem h2 h3

end CFSG.OddStandard.SmallF3.Omega
