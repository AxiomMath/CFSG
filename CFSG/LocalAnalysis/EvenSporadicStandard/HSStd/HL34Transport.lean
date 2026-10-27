module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Action
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Cent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Class
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Spec
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S6Perm

public section

namespace CFSG.EvenSporadicStandard.HSStd.HL34

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Subgroup

theorem hl34_step
    (h : hl34Check enumR.tabs (orbitR r₂T).tabs (orbitR r₄T).tabs = true)
    {t u w : R} (ht : IsConj t r₃R) (ht2 : t * t = 1) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hut : u ≠ t) (hut' : u * t = t * u) (hw1 : w ≠ 1) (hw3 : w ^ 3 = 1)
    (hwt : w * t = t * w) (hwu : w * u = u * w) :
    ∃ o ∈ ({u, t * u} : Set R), IsConj o r₂R ∧ IsConj (t * o) r₄R := by
  obtain ⟨c, hc⟩ := isConj_iff.1 ht
  have hcomm : ∀ a b : R, a * b = b * a →
      (c * a * c⁻¹) * (c * b * c⁻¹) = (c * b * c⁻¹) * (c * a * c⁻¹) := fun a b hab => by
    calc (c * a * c⁻¹) * (c * b * c⁻¹) = c * (a * b) * c⁻¹ := by group
      _ = c * (b * a) * c⁻¹ := by rw [hab]
      _ = (c * b * c⁻¹) * (c * a * c⁻¹) := by group
  have hne : ∀ a b : R, a ≠ b → c * a * c⁻¹ ≠ c * b * c⁻¹ := fun a b hab h' => by
    apply hab
    have := congrArg (fun z => c⁻¹ * z * c) h'
    simpa [mul_assoc] using this
  have hx := hl34Check_spec h (x := c * u * c⁻¹) (w := c * w * c⁻¹)
    (by rw [← hc]; exact hcomm u t hut')
    (by calc c * u * c⁻¹ * (c * u * c⁻¹) = c * (u * u) * c⁻¹ := by group
          _ = 1 := by rw [hu2]; group)
    (by simpa using hne u 1 hu1)
    (by rw [← hc]; exact hne u t hut)
    (by simpa using hne w 1 hw1)
    (by rw [conj_pow, hw3]; group)
    (by rw [← hc]; exact hcomm w t hwt)
    (hcomm w u hwu)
  have hu : IsConj u (c * u * c⁻¹) := isConj_iff.2 ⟨c, rfl⟩
  have htu : IsConj (t * u) (r₃R * (c * u * c⁻¹)) := isConj_iff.2 ⟨c, by
    rw [← hc]; group⟩
  have htt : t * (t * u) = u := by rw [← mul_assoc, ht2, one_mul]
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨u, Or.inl rfl, hu.trans h1, htu.trans h2⟩
  · exact ⟨t * u, Or.inr rfl, htu.trans h2, by rw [htt]; exact hu.trans h1⟩

section Transport

variable {D : Type*} [Group D] (H : Subgroup D) [H.Normal] (ψ : ↥H ≃* ↥S) (e : ↥R ≃* MulAut ↥S)
  (he : ∀ (r : ↥R) (s : ↥S), ((e r s : ↥S) : Equiv.Perm (Fin 42)) = r * s * r⁻¹)
include he

theorem rho_conj (d : D) (h : H) :
    ((rho H ψ e d : ↥R) : Equiv.Perm (Fin 42)) * (ψ h : Equiv.Perm (Fin 42)) *
        ((rho H ψ e d : ↥R) : Equiv.Perm (Fin 42))⁻¹ =
      (ψ (MulAut.conjNormal d h) : Equiv.Perm (Fin 42)) := by
  have h1 := he (rho H ψ e d) (ψ h)
  rw [rho_apply] at h1
  simpa using h1.symm

theorem mem_centralizer_iff_rho (o : D) (h : H) :
    (h : D) ∈ centralizer ({o} : Set D) ↔
      (ψ h : Equiv.Perm (Fin 42)) ∈
        centralizer ({((rho H ψ e o : ↥R) : Equiv.Perm (Fin 42))} : Set (Equiv.Perm (Fin 42))) := by
  have key := rho_conj H ψ e he o h
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hc
    have hc' : MulAut.conjNormal o h = h :=
      Subtype.ext (by rw [MulAut.conjNormal_apply]; exact mul_inv_eq_iff_eq_mul.2 hc.symm)
    rw [hc'] at key
    exact (mul_inv_eq_iff_eq_mul.1 key).symm
  · intro hc
    have hc' : MulAut.conjNormal o h = h := by
      apply ψ.injective
      apply Subtype.ext
      rw [← key]
      exact mul_inv_eq_iff_eq_mul.2 hc.symm
    have := congrArg Subtype.val hc'
    rw [MulAut.conjNormal_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm

theorem card_inf_centralizer_rho (o : D) :
    Nat.card ↥(H ⊓ centralizer ({o} : Set D)) =
      Nat.card ↥(centralizer ({((rho H ψ e o : ↥R) : Equiv.Perm (Fin 42))} :
        Set (Equiv.Perm (Fin 42))) ⊓ S) := by
  let e1 : ↥(H ⊓ centralizer ({o} : Set D)) ≃ {h : ↥H // (h : D) ∈ centralizer ({o} : Set D)} :=
    ⟨fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩, fun y => ⟨y.1.1, y.1.2, y.2⟩, fun _ => rfl, fun _ => rfl⟩
  let e2 : {h : ↥H // (h : D) ∈ centralizer ({o} : Set D)} ≃ {s : ↥S //
      (s : Equiv.Perm (Fin 42)) ∈ centralizer ({((rho H ψ e o : ↥R) : Equiv.Perm (Fin 42))} :
        Set (Equiv.Perm (Fin 42)))} :=
    ψ.toEquiv.subtypeEquiv (mem_centralizer_iff_rho H ψ e he o)
  let e3 : {s : ↥S // (s : Equiv.Perm (Fin 42)) ∈
      centralizer ({((rho H ψ e o : ↥R) : Equiv.Perm (Fin 42))} : Set (Equiv.Perm (Fin 42)))} ≃
      ↥(centralizer ({((rho H ψ e o : ↥R) : Equiv.Perm (Fin 42))} :
        Set (Equiv.Perm (Fin 42))) ⊓ S) :=
    ⟨fun s => ⟨s.1, s.2, s.1.2⟩, fun y => ⟨⟨y, y.2.2⟩, y.2.1⟩, fun _ => rfl, fun _ => rfl⟩
  exact Nat.card_congr (e1.trans (e2.trans e3))

end Transport

theorem hl34_main
    (hcheck : hl34Check enumR.tabs (orbitR r₂T).tabs (orbitR r₄T).tabs = true)
    {D : Type} [Group D] [Finite D]
    (hZ : ∀ N : Subgroup D, N.Normal → Odd (Nat.card N) → N = ⊥)
    {t : D} (ht : orderOf t = 2) {K : Subgroup D}
    (hC : centralizer ({t} : Set D) = zpowers t ⊔ K) (hd : Disjoint (zpowers t) K)
    (eK : ↥K ≃* Equiv.Perm (Fin 5)) (H : Subgroup D) [H.Normal] (ψ : ↥H ≃* ↥S)
    {u : D} (hu : u ∈ K) (hsw : (eK ⟨u, hu⟩).IsSwap) :
    ∃ o ∈ ({u, t * u} : Set D), 7 ∣ Nat.card ↥(centralizer ({o} : Set D)) ∧
      ¬ ∃ g ∈ centralizer ({o} : Set D), g * t * g⁻¹ = t * o := by
  obtain ⟨e, he, -⟩ := full_automorphism_action
  have hHcard : Nat.card H = 20160 := by rw [Nat.card_congr ψ.toEquiv]; exact card_S
  have hCcard := card_centralizer_eq ht hC hd eK
  have hKC : K ≤ centralizer ({t} : Set D) := le_sup_right.trans hC.ge
  have ht2 : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  have hρt2 : rho H ψ e t * rho H ψ e t = 1 := by rw [← map_mul, ht2, map_one]
  have hH : ¬ H ≤ centralizer ({t} : Set D) := by
    intro hle
    have := Subgroup.card_le_of_le hle
    omega
  have hX : 24 < Nat.card ↥(H ⊓ centralizer ({t} : Set D)) := by
    rw [card_inf_centralizer_rho H ψ e he t]
    have := sixty_le_card_inf_centralizer (rho H ψ e t) hρt2
    omega
  have hinj : Function.Injective (rho H ψ e) :=
    rho_injective H ψ e (centralizer_eq_bot_of_normal hZ ht hC hd eK H hH hX)
  have hρt : orderOf (rho H ψ e t) = 2 := by rw [orderOf_injective _ hinj t, ht]
  have hdvd : 240 ∣ Nat.card ↥(centralizer ({rho H ψ e t} : Set ↥R)) := by
    have hle : (centralizer ({t} : Set D)).map (rho H ψ e) ≤
        centralizer ({rho H ψ e t} : Set ↥R) := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ centralizer ({t} : Set D) := hx
      rw [mem_centralizer_singleton_iff] at hx' ⊢
      rw [← map_mul, ← map_mul, hx']
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective hinj, hCcard] at this
  have hconj := isConj_r₃_of_dvd hρt hdvd
  obtain ⟨a, b, hab, hσ⟩ := hsw
  have huu : u * u = 1 := by
    have h1 : eK (⟨u, hu⟩ * ⟨u, hu⟩) = eK 1 := by
      rw [map_mul, hσ, Equiv.swap_mul_self, map_one]
    exact congrArg Subtype.val (eK.injective h1)
  have hu1 : u ≠ 1 := by
    intro h
    have h1 : eK ⟨u, hu⟩ = 1 := by
      have : (⟨u, hu⟩ : ↥K) = 1 := Subtype.ext h
      rw [this, map_one]
    rw [hσ] at h1
    have h2 := congrArg (fun f : Equiv.Perm (Fin 5) => f a) h1
    simp at h2
    exact hab h2.symm
  have hut : u ≠ t := by
    intro h
    have h1 : t ∈ zpowers t ⊓ K := ⟨mem_zpowers t, h ▸ hu⟩
    rw [disjoint_iff.1 hd, mem_bot] at h1
    rw [h1, orderOf_one] at ht
    omega
  obtain ⟨ρ₀, hρ3, hρ1, hρc⟩ :=
    CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.s6_exists_rho a b hab
  have hκ3 : eK.symm ρ₀ ^ 3 = 1 :=
    eK.injective (by rw [map_pow, MulEquiv.apply_symm_apply, hρ3, map_one])
  have hκ1 : eK.symm ρ₀ ≠ 1 := fun h => hρ1 (by simpa using congrArg eK h)
  have hκu : eK.symm ρ₀ * ⟨u, hu⟩ = ⟨u, hu⟩ * eK.symm ρ₀ :=
    eK.injective (by rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hσ, hρc])
  have hw3 : ((eK.symm ρ₀ : ↥K) : D) ^ 3 = 1 := congrArg Subtype.val hκ3
  have hw1 : ((eK.symm ρ₀ : ↥K) : D) ≠ 1 := fun h => hκ1 (Subtype.ext h)
  have hwu : ((eK.symm ρ₀ : ↥K) : D) * u = u * ((eK.symm ρ₀ : ↥K) : D) :=
    congrArg Subtype.val hκu
  have hwt : ((eK.symm ρ₀ : ↥K) : D) * t = t * ((eK.symm ρ₀ : ↥K) : D) :=
    (mem_centralizer_iff.1 (hKC (eK.symm ρ₀).2) t rfl).symm
  have hut' : u * t = t * u := (mem_centralizer_iff.1 (hKC hu) t rfl).symm
  obtain ⟨o', ho', hc2, hc4⟩ := hl34_step hcheck hconj hρt2
    (by rw [← map_mul, huu, map_one])
    (fun h => hu1 (hinj (h.trans (map_one _).symm)))
    (fun h => hut (hinj h))
    (by rw [← map_mul, ← map_mul, hut'])
    (fun h => hw1 (hinj (h.trans (map_one _).symm)))
    (by rw [← map_pow, hw3, map_one])
    (by rw [← map_mul, ← map_mul, hwt])
    (by rw [← map_mul, ← map_mul, hwu])
  have hex : ∃ o ∈ ({u, t * u} : Set D), rho H ψ e o = o' := by
    rcases ho' with rfl | rfl
    · exact ⟨u, Or.inl rfl, rfl⟩
    · exact ⟨t * u, Or.inr rfl, map_mul _ t u⟩
  obtain ⟨o, hoD, rfl⟩ := hex
  refine ⟨o, hoD, ?_, ?_⟩
  · have hcard := card_inf_centralizer_rho H ψ e he o
    rw [card_inf_centralizer_of_isConj_r₂ hc2] at hcard
    have hdvd' : Nat.card ↥(H ⊓ centralizer ({o} : Set D)) ∣
        Nat.card ↥(centralizer ({o} : Set D)) := Subgroup.card_dvd_of_le inf_le_right
    rw [hcard] at hdvd'
    exact dvd_trans (by norm_num : 7 ∣ 168) hdvd'
  · rintro ⟨g, -, hg⟩
    have h1 : rho H ψ e g * rho H ψ e t * (rho H ψ e g)⁻¹ = rho H ψ e t * rho H ψ e o := by
      simpa [map_mul, map_inv] using congrArg (rho H ψ e) hg
    exact not_isConj₃₄ (hconj.symm.trans ((isConj_iff.2 ⟨_, h1⟩).trans hc4))

end CFSG.EvenSporadicStandard.HSStd.HL34
