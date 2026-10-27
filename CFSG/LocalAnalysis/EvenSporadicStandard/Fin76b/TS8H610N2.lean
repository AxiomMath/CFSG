module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H610C
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H610N
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Sigma

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OHyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B : Subgroup G} {S : Subgroup G}
  (h : OHyp69 L z t T E B β S)

include h

theorem card_Fsub (hM : OuterMFacts E S z t) {α : G} (hα : AlphaSpec S z t α) :
    Nat.card ↥(Fsub h hα) = 2048 := by
  have horb := card_conj_orbit_mul_card_cent (Fsub h hα) z
  rw [h.card_CFz hM hα] at horb
  have hX : Set.ncard {u : G | ∃ f ∈ Fsub h hα, u = f * z * f⁻¹} ≤ 32 := by
    rw [← h.X_card hα]
    exact Set.ncard_le_ncard (fun u hu => h.Oz_sub_X hα hu) (Set.toFinite _)
  have hle := h.card_M_le_F hα
  rw [hM.cardM] at hle
  omega

theorem F_pgroup (hM : OuterMFacts E S z t) {α : G} (hα : AlphaSpec S z t α) :
    IsPGroup 2 (Fsub h hα) :=
  IsPGroup.of_card (n := 11) (by rw [h.card_Fsub hM hα]; norm_num)

theorem card_QF (hM : OuterMFacts E S z t) {α : G} (hα : AlphaSpec S z t α) :
    Nat.card ↥(Fsub h hα ⊓ centralizer ({α} : Set G)) = 1024 := by
  have horb := card_conj_orbit_mul_card_cent (Fsub h hα) α
  rw [h.alpha_orbit_F hα, Set.ncard_pair (fun h1 => h.t_ne
    (mul_left_cancel ((mul_one α).trans h1)).symm), h.card_Fsub hM hα] at horb
  omega

theorem sigma_not_FB (hM : OuterMFacts E S z t) {α : G} (hα : AlphaSpec S z t α) {σ : G}
    (hσ : OuterSigma L z T E S α σ) {f b : G} (hf : f ∈ Fsub h hα) (hb : b ∈ B) :
    σ ≠ f * b := by
  intro hσfb
  have hbW := h.B_le_W hb
  have hbN : b ∈ normalizer (E : Set G) := h.wf.cent_le_normalizer hbW
  have hfσ : f = σ * b⁻¹ := by rw [hσfb]; group
  have hfN : f ∈ normalizer (E : Set G) := by
    rw [hfσ]; exact mul_mem hσ.norm_E (inv_mem hbN)
  obtain ⟨e', he', hfe⟩ := h.Fnorm_inner hM hα hf hfN
  have hcE : e'⁻¹ * f ∈ centralizer (E : Set G) := by
    refine mem_centralizer_iff.2 fun x hx => ?_
    have h1 := hfe x hx
    calc x * (e'⁻¹ * f) = e'⁻¹ * (e' * x * e'⁻¹) * f := by group
      _ = e'⁻¹ * (f * x * f⁻¹) * f := by rw [h1]
      _ = e'⁻¹ * f * x := by group
  have hbz : b * z = z * b := h.BS b hb z h.zS
  have hbzi : b⁻¹ * z = z * b⁻¹ := by
    calc b⁻¹ * z = b⁻¹ * (z * b) * b⁻¹ := by group
      _ = b⁻¹ * (b * z) * b⁻¹ := by rw [hbz]
      _ = z * b⁻¹ := by group
  have he'z : e'⁻¹ * z = z * e'⁻¹ := h.oe.cfg.z_comm_of_mem_A (h.oe.E_le_L (inv_mem he'))
  have hfz : f * z = z * f := by
    rw [hfσ]
    calc σ * b⁻¹ * z = σ * (b⁻¹ * z) := by group
      _ = σ * (z * b⁻¹) := by rw [hbzi]
      _ = (σ * z) * b⁻¹ := by group
      _ = (z * σ) * b⁻¹ := by rw [hσ.comm_z]
      _ = z * (σ * b⁻¹) := by group
  have hcz : e'⁻¹ * f * z = z * (e'⁻¹ * f) := by
    calc e'⁻¹ * f * z = e'⁻¹ * (f * z) := by group
      _ = e'⁻¹ * (z * f) := by rw [hfz]
      _ = (e'⁻¹ * z) * f := by group
      _ = (z * e'⁻¹) * f := by rw [he'z]
      _ = z * (e'⁻¹ * f) := by group
  apply hσ.not_mem
  have hzL : z ∈ L ⊔ zpowers z := mem_sup_right (mem_zpowers z)
  have htL : t ∈ L ⊔ zpowers z := mem_sup_left (h.oe.cfg.t_mem_A)
  have hcmem : e'⁻¹ * f ∈ L ⊔ zpowers z := by
    rcases hM.centZ _ hcE hcz with h1 | h1 | h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact hzL
    · rw [h1]; exact htL
    · rw [h1]; exact mul_mem htL hzL
  have hσeq : σ = e' * (e'⁻¹ * f) * b := by rw [hσfb]; group
  rw [hσeq]
  exact mul_mem (mul_mem (mem_sup_left (h.oe.E_le_L he')) hcmem) (mem_sup_left (h.ob.B_le hb))


omit h in
theorem sigma_mem_M {α σ : G} (hσ : OuterSigma L z T E S α σ) :
    σ ∈ normalizer ((S ⊔ E : Subgroup G) : Set G) := by
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ.sq
  have hnE : ∀ e ∈ E, σ * e * σ⁻¹ ∈ E := fun e he => (mem_normalizer_iff.1 hσ.norm_E e).1 he
  have hnE' : ∀ e ∈ E, σ⁻¹ * e * σ ∈ E := fun e he => by
    have := (mem_normalizer_iff.1 (inv_mem hσ.norm_E : σ⁻¹ ∈ normalizer (E : Set G)) e).1 he
    simpa using this
  have hnS : ∀ s ∈ S, σ * s * σ⁻¹ ∈ S := hσ.norm_S
  have hnS' : ∀ s ∈ S, σ⁻¹ * s * σ ∈ S := fun s hs => by
    rw [hσi]; have := hσ.norm_S s hs; rwa [hσi] at this
  rw [mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    have hle : S ⊔ E ≤ (S ⊔ E).comap (MulAut.conj σ).toMonoidHom :=
      sup_le (fun s hs => mem_sup_left (hnS s hs)) (fun e he => mem_sup_right (hnE e he))
    exact hle hu
  · intro hu
    have hle : S ⊔ E ≤ (S ⊔ E).comap (MulAut.conj σ⁻¹).toMonoidHom :=
      sup_le (fun s hs => mem_sup_left (by simpa using hnS' s hs))
        (fun e he => mem_sup_right (by simpa using hnE' e he))
    have := hle hu
    simpa [mul_assoc] using this

include h in
theorem M_eq_FB (hM : OuterMFacts E S z t) {α : G} (hα : AlphaSpec S z t α) {σ : G}
    (hσ : OuterSigma L z T E S α σ) {m : G}
    (hm : m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G)) :
    ∃ f ∈ Fsub h hα, ∃ b ∈ B, m = f * b ∨ m = f * b * σ := by
  classical
  have hσM := sigma_mem_M hσ
  have hFB : ∀ (f : ↥(Fsub h hα)) (b : ↥B),
      (f : G) * b ∈ normalizer ((S ⊔ E : Subgroup G) : Set G) := fun f b =>
    mul_mem (h.Fsub_le_M hα f.2) (h.W_mem_M (h.B_le_W b.2))
  have inj0 : ∀ (f f' : ↥(Fsub h hα)) (b b' : ↥B), (f : G) * b = f' * b' → f = f' ∧ b = b' := by
    intro f f' b b' h1
    have h2 : ((f' : G)⁻¹ * f : G) = b' * (b : G)⁻¹ := by
      calc (f' : G)⁻¹ * f = (f' : G)⁻¹ * (f * b) * (b : G)⁻¹ := by group
        _ = (f' : G)⁻¹ * (f' * b') * (b : G)⁻¹ := by rw [h1]
        _ = b' * (b : G)⁻¹ := by group
    have hbB : (b' : G) * (b : G)⁻¹ ∈ B := mul_mem b'.2 (inv_mem b.2)
    have hbF : (b' : G) * (b : G)⁻¹ ∈ Fsub h hα := by
      rw [← h2]; exact mul_mem (inv_mem f'.2) f.2
    have h3 := h.B_inf_F hα hbB hbF
    have hb : (b' : G) = b := by
      calc (b' : G) = (b' * (b : G)⁻¹) * b := by group
        _ = b := by rw [h3, one_mul]
    have hf : (f : G) = f' := by
      calc (f : G) = f' * ((f' : G)⁻¹ * f) := by group
        _ = f' := by rw [h2, h3, mul_one]
    exact ⟨Subtype.ext hf, Subtype.ext hb.symm⟩
  have cross : ∀ (f f' : ↥(Fsub h hα)) (b b' : ↥B),
      (f : G) * (b : G) ≠ (f' : G) * (b' : G) * σ := by
    intro f f' b b' h1
    have hσeq : σ = ((b' : G)⁻¹ * ((f' : G)⁻¹ * (f : G)) * ((b' : G)⁻¹)⁻¹) *
        ((b' : G)⁻¹ * (b : G)) := by
      calc σ = ((f' : G) * (b' : G))⁻¹ * ((f' : G) * (b' : G) * σ) := by group
        _ = ((f' : G) * (b' : G))⁻¹ * ((f : G) * (b : G)) := by rw [h1]
        _ = _ := by group
    have hb'M : (b' : G)⁻¹ ∈ normalizer ((S ⊔ E : Subgroup G) : Set G) :=
      inv_mem (h.W_mem_M (h.B_le_W b'.2))
    have hg : (f' : G)⁻¹ * f ∈ Fsub h hα := mul_mem (inv_mem f'.2) f.2
    have hf'' := h.Fsub_normal hα hb'M hg
    exact h.sigma_not_FB hM hα hσ hf'' (mul_mem (inv_mem b'.2) b.2) hσeq
  let Φ : (↥(Fsub h hα) × ↥B) ⊕ (↥(Fsub h hα) × ↥B) →
      ↥(normalizer ((S ⊔ E : Subgroup G) : Set G)) := fun p =>
    match p with
    | Sum.inl p => ⟨(p.1 : G) * p.2, hFB p.1 p.2⟩
    | Sum.inr p => ⟨(p.1 : G) * p.2 * σ, mul_mem (hFB p.1 p.2) hσM⟩
  have hinj : Function.Injective Φ := by
    rintro (⟨f, b⟩ | ⟨f, b⟩) (⟨f', b'⟩ | ⟨f', b'⟩) hΦ
    · have h1 : (f : G) * b = f' * b' := congrArg Subtype.val hΦ
      obtain ⟨e1, e2⟩ := inj0 f f' b b' h1
      rw [e1, e2]
    · exact absurd (congrArg Subtype.val hΦ) (cross f f' b b')
    · exact absurd (congrArg Subtype.val hΦ).symm (cross f' f b' b)
    · have h1 : (f : G) * b * σ = f' * b' * σ := congrArg Subtype.val hΦ
      obtain ⟨e1, e2⟩ := inj0 f f' b b' (mul_right_cancel h1)
      rw [e1, e2]
  have hcard : Nat.card ↥(normalizer ((S ⊔ E : Subgroup G) : Set G)) ≤
      Nat.card ((↥(Fsub h hα) × ↥B) ⊕ (↥(Fsub h hα) × ↥B)) := by
    rw [Nat.card_sum, Nat.card_prod, h.card_Fsub hM hα, h.B_card, hM.cardM]
  have hbij := hinj.bijective_of_nat_card_le hcard
  obtain ⟨p, hp⟩ := hbij.2 ⟨m, hm⟩
  rcases p with ⟨f, b⟩ | ⟨f, b⟩
  · exact ⟨f, f.2, b, b.2, Or.inl (congrArg Subtype.val hp).symm⟩
  · exact ⟨f, f.2, b, b.2, Or.inr (congrArg Subtype.val hp).symm⟩

end OHyp69

end CFSG.EvenSporadicStandard.Fin76b
