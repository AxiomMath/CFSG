module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316Z1

public section

namespace CFSG.OddStandard.SmallF3.FritzII

variable {G : Type} [Group G] {t tau lam rho : G} {Z E W Q R T P : Subgroup G}

@[expose] def fzrASig (rho p : G) : G := rho * p * rho⁻¹

private lemma fzrASig_mul (rho x y : G) :
    fzrASig rho (x * y) = fzrASig rho x * fzrASig rho y := by
  simp only [fzrASig]; group

private lemma fzrASig_mul3 (rho x y z : G) :
    fzrASig rho (x * y * z)
      = fzrASig rho x * fzrASig rho y * fzrASig rho z := by
  simp only [fzrASig]; group

private lemma fzrASig_inv (rho x : G) :
    fzrASig rho x⁻¹ = (fzrASig rho x)⁻¹ := by
  simp only [fzrASig]; group

private lemma fzrASig_rho_ord {rho p : G} (h : rho ^ 3 = 1) :
    fzrASig rho (fzrASig rho (fzrASig rho p)) = p := by
  have hrho : rho * rho * rho = 1 := by rw [← pow_three', h]
  simp only [fzrASig]
  rw [show rho * (rho * (rho * p * rho⁻¹) * rho⁻¹) * rho⁻¹
      = (rho * rho * rho) * p * (rho * rho * rho)⁻¹ by group, hrho]
  group

private lemma fzrAux_norm (hs : FzStr t tau lam rho Z E W Q R T)
    (hpf : FzPFacts t tau rho E W Q T P) (h8 : FzZ8 Z E P) {p : G} (hp : p ∈ P) :
    p * fzrASig rho p * fzrASig rho (fzrASig rho p) = 1 := by
  have hp1 : fzrASig rho p ∈ P := hpf.nrm_P_rho p hp
  have hp2 : fzrASig rho (fzrASig rho p) ∈ P := hpf.nrm_P_rho _ hp1
  have hnP : p * fzrASig rho p * fzrASig rho (fzrASig rho p) ∈ P :=
    P.mul_mem (P.mul_mem hp hp1) hp2
  have hfix : fzrASig rho (p * fzrASig rho p * fzrASig rho (fzrASig rho p))
      = p * fzrASig rho p * fzrASig rho (fzrASig rho p) := by
    rw [fzrASig_mul3, fzrASig_rho_ord hs.rho_ord]
    calc fzrASig rho p * fzrASig rho (fzrASig rho p) * p
        = fzrASig rho p * (fzrASig rho (fzrASig rho p) * p) := by rw [mul_assoc]
      _ = fzrASig rho p * (p * fzrASig rho (fzrASig rho p)) := by
            rw [h8.comm (fzrASig rho (fzrASig rho p)) hp2 p hp]
      _ = (fzrASig rho p * p) * fzrASig rho (fzrASig rho p) := by rw [← mul_assoc]
      _ = (p * fzrASig rho p) * fzrASig rho (fzrASig rho p) := by
            rw [h8.comm (fzrASig rho p) hp1 p hp]
  exact hpf.rho_fpf _ hnP hfix

lemma fzr_a_pow8 (hs : FzStr t tau lam rho Z E W Q R T)
    (hpf : FzPFacts t tau rho E W Q T P) {p : G} (hp : p ∈ P) : p ^ 8 = 1 := by
  have h2 : p ^ 2 ∈ E := hpf.P_sq p hp
  have h4 : (p ^ 2) ^ 4 = 1 := hs.E_exp (p ^ 2) h2
  have h : (p ^ 2) ^ 4 = p ^ 8 := by rw [← pow_mul]
  rw [← h]; exact h4

lemma fzr_a_sig_b (hs : FzStr t tau lam rho Z E W Q R T)
    (hpf : FzPFacts t tau rho E W Q T P) (h8 : FzZ8 Z E P) {a b : G} (haP : a ∈ P)
    (hσa : fzrASig rho a = b) : fzrASig rho b = (a * b)⁻¹ := by
  have hnorm : a * fzrASig rho a * fzrASig rho (fzrASig rho a) = 1 :=
    fzrAux_norm hs hpf h8 haP
  rw [hσa] at hnorm
  have h1 : a * b = (fzrASig rho b)⁻¹ := by
    calc a * b = (a * b) * fzrASig rho b * (fzrASig rho b)⁻¹ := by group
      _ = 1 * (fzrASig rho b)⁻¹ := by rw [hnorm]
      _ = (fzrASig rho b)⁻¹ := one_mul _
  rw [h1, inv_inv]

private def fzrAuxPhi (rho p : G) : G := p * (fzrASig rho p)⁻¹

private lemma fzrAuxPhi_mem (hpf : FzPFacts t tau rho E W Q T P) {p : G} (hp : p ∈ P) :
    fzrAuxPhi rho p ∈ P :=
  P.mul_mem hp (P.inv_mem (hpf.nrm_P_rho p hp))

private lemma fzrAuxPhi_inj (hpf : FzPFacts t tau rho E W Q T P) {p q : G}
    (hp : p ∈ P) (hq : q ∈ P) (h : fzrAuxPhi rho p = fzrAuxPhi rho q) : p = q := by
  have hpq : p * (fzrASig rho p)⁻¹ = q * (fzrASig rho q)⁻¹ := by
    simpa only [fzrAuxPhi] using h
  have key : q⁻¹ * p = (fzrASig rho q)⁻¹ * fzrASig rho p := by
    calc q⁻¹ * p
        = q⁻¹ * (p * (fzrASig rho p)⁻¹) * fzrASig rho p := by group
      _ = q⁻¹ * (q * (fzrASig rho q)⁻¹) * fzrASig rho p := by rw [hpq]
      _ = (fzrASig rho q)⁻¹ * fzrASig rho p := by group
  have hfix : fzrASig rho (q⁻¹ * p) = q⁻¹ * p := by
    rw [fzrASig_mul, fzrASig_inv, key]
  have h1 : q⁻¹ * p = 1 :=
    hpf.rho_fpf (q⁻¹ * p) (P.mul_mem (P.inv_mem hq) hp) hfix
  calc p = q * (q⁻¹ * p) := by group
    _ = q * 1 := by rw [h1]
    _ = q := mul_one q

private lemma fzrAuxPhi_sq (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hpf : FzPFacts t tau rho E W Q T P) {d : G} (hd : d ∈ P) :
    fzrAuxPhi rho d ^ 2 = fzrAuxPhi rho (d ^ 2) := by
  have hs_inv : (fzrASig rho d)⁻¹ ∈ P := P.inv_mem (hpf.nrm_P_rho d hd)
  have hcs : (fzrASig rho d)⁻¹ * d = d * (fzrASig rho d)⁻¹ :=
    hcomm (fzrASig rho d)⁻¹ hs_inv d hd
  rw [pow_two, fzrAuxPhi, fzrAuxPhi, show d ^ 2 = d * d by rw [pow_two],
    fzrASig_mul, mul_inv_rev]
  calc (d * (fzrASig rho d)⁻¹) * (d * (fzrASig rho d)⁻¹)
      = d * ((fzrASig rho d)⁻¹ * d) * (fzrASig rho d)⁻¹ := by group
    _ = d * (d * (fzrASig rho d)⁻¹) * (fzrASig rho d)⁻¹ := by rw [hcs]
    _ = (d * d) * ((fzrASig rho d)⁻¹ * (fzrASig rho d)⁻¹) := by group

private lemma fzrAuxPhi_surj (hpf : FzPFacts t tau rho E W Q T P) :
    ∀ c ∈ P, ∃ d ∈ P, fzrAuxPhi rho d = c := by
  have hcard : Nat.card ↥P = 64 := hpf.card_P
  haveI : Finite ↥P := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hinj : Function.Injective
      (fun p : ↥P => (⟨fzrAuxPhi rho p.1, fzrAuxPhi_mem hpf p.2⟩ : ↥P)) := by
    intro p q hpq
    exact Subtype.ext (fzrAuxPhi_inj hpf p.2 q.2 (congrArg Subtype.val hpq))
  have hsurj := Finite.surjective_of_injective hinj
  intro c hc
  obtain ⟨d, hd⟩ := hsurj ⟨c, hc⟩
  exact ⟨d.1, d.2, congrArg Subtype.val hd⟩

lemma fzr_a_exists_notE (hs : FzStr t tau lam rho Z E W Q R T)
    (hpf : FzPFacts t tau rho E W Q T P) : ∃ a ∈ P, a ∉ E := by
  by_contra h
  push Not at h
  have hle : P ≤ E := fun x hx => h x hx
  haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hs.card_E]; norm_num)
  have hinj : Function.Injective (fun p : ↥P => (⟨(p : G), hle p.2⟩ : ↥E)) := by
    intro p q hpq
    exact Subtype.ext (by
      have h := congrArg (fun x : ↥E => (x : G)) hpq
      simpa using h)
  have hcard := Nat.card_le_card_of_injective (fun p : ↥P => (⟨(p : G), hle p.2⟩ : ↥E)) hinj
  rw [hpf.card_P, hs.card_E] at hcard
  omega

lemma fzr_a_b_notE (hs : FzStr t tau lam rho Z E W Q R T) {a b : G} (haE : a ∉ E)
    (hσa : fzrASig rho a = b) : b ∉ E := by
  intro hbE
  have h1 : fzrASig rho b ∈ E := hs.rho_nrm_E b hbE
  have h2 : fzrASig rho (fzrASig rho b) ∈ E := hs.rho_nrm_E _ h1
  have h3 : fzrASig rho (fzrASig rho b) = a := by
    rw [← hσa, fzrASig_rho_ord hs.rho_ord]
  exact haE (h3 ▸ h2)

lemma fzr_a_ab_notE (hs : FzStr t tau lam rho Z E W Q R T)
    (hpf : FzPFacts t tau rho E W Q T P) (h8 : FzZ8 Z E P) {a b : G} (haP : a ∈ P)
    (haE : a ∉ E) (hσa : fzrASig rho a = b) : a * b ∉ E := by
  have hnorm : a * fzrASig rho a * fzrASig rho (fzrASig rho a) = 1 :=
    fzrAux_norm hs hpf h8 haP
  rw [hσa] at hnorm
  have h1 : fzrASig rho b = (a * b)⁻¹ := fzr_a_sig_b hs hpf h8 haP hσa
  intro habE
  have hσbE : fzrASig rho b ∈ E := by rw [h1]; exact E.inv_mem habE
  have h3 : fzrASig rho (fzrASig rho b) = a := by
    have hbσ : b * fzrASig rho b = a⁻¹ := by
      rw [show b * fzrASig rho b = a⁻¹ * (a * b * fzrASig rho b) by group, hnorm,
        mul_one]
    rw [h1, fzrASig_inv, fzrASig_mul, hσa, hbσ, inv_inv]
  have h2 : fzrASig rho (fzrASig rho b) ∈ E := hs.rho_nrm_E _ hσbE
  exact haE (h3 ▸ h2)

lemma fzr_a_haib_notE (hs : FzStr t tau lam rho Z E W Q R T)
    (hpf : FzPFacts t tau rho E W Q T P) (h8 : FzZ8 Z E P)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {a b : G} (haP : a ∈ P) (hbP : b ∈ P)
    (haE : a ∉ E) (hσa : fzrASig rho a = b) : a⁻¹ * b ∉ E := by
  intro hE
  have hcomm_ba : b⁻¹ * a = a * b⁻¹ := hcomm b⁻¹ (P.inv_mem hbP) a haP
  have hab' : a * b⁻¹ ∈ E := by
    have h1 : b⁻¹ * a ∈ E := by
      have h := E.inv_mem hE
      simpa [mul_inv_rev] using h
    rwa [hcomm_ba] at h1
  obtain ⟨c, hcP, hc2⟩ := h8.sq (a * b⁻¹) hab'
  obtain ⟨d, hdP, hd_eq⟩ := fzrAuxPhi_surj hpf c hcP
  have hφa : fzrAuxPhi rho a = c ^ 2 := by
    rw [fzrAuxPhi, hσa, hc2]
  have hφd : fzrAuxPhi rho (d ^ 2) = c ^ 2 := by
    rw [← fzrAuxPhi_sq hcomm hpf hdP, hd_eq]
  have hd2P : d ^ 2 ∈ P := P.pow_mem hdP 2
  have ha_eq : a = d ^ 2 := fzrAuxPhi_inj hpf haP hd2P (by rw [hφa, hφd])
  exact haE (by rw [ha_eq]; exact hpf.P_sq d hdP)

end CFSG.OddStandard.SmallF3.FritzII
