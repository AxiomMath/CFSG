module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRB1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316P2

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

private lemma fzrAux_conj_mem {G : Type} [Group G] {X P : Subgroup G} (hXP : X ≤ P)
    (hX : ∀ x : G, x ∈ X ↔ x ∈ P ∧ x * x = 1) {g : G}
    (hg : ∀ p ∈ P, g * p * g⁻¹ ∈ P) {x : G} (hx : x ∈ X) : g * x * g⁻¹ ∈ X := by
  have hxP : x ∈ P := hXP hx
  have hx2 : x * x = 1 := ((hX x).mp hx).2
  rw [hX]
  refine ⟨hg x hxP, ?_⟩
  calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
    _ = 1 := by rw [hx2]; group

private def fzrAux_conjX {G : Type} [Group G] {X P : Subgroup G} (hXP : X ≤ P)
    (hX : ∀ x : G, x ∈ X ↔ x ∈ P ∧ x * x = 1) (g : G)
    (hg : ∀ p ∈ P, g * p * g⁻¹ ∈ P) : X →* X where
  toFun x := ⟨g * (x : G) * g⁻¹, fzrAux_conj_mem hXP hX hg x.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by
    apply Subtype.ext
    change g * ((a : G) * (b : G)) * g⁻¹ = (g * (a : G) * g⁻¹) * (g * (b : G) * g⁻¹)
    group

private def fzrAux_commMap {H : Type} [CommGroup H] (A : H →* H) : H →* H where
  toFun x := A x * x⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_inv_rev]
    ac_rfl

private lemma fzrAux_commMap_apply {H : Type} [CommGroup H] (A : H →* H) (x : H) :
    fzrAux_commMap A x = A x * x⁻¹ := rfl

private lemma fzrAux_conj_conj {G : Type} [Group G] {g h y : G}
    (hgh : g * h * g⁻¹ = h) :
    g * (h * y * h⁻¹) * g⁻¹ = h * (g * y * g⁻¹) * h⁻¹ := by
  calc g * (h * y * h⁻¹) * g⁻¹
      = (g * h * g⁻¹) * (g * y * g⁻¹) * (g * h * g⁻¹)⁻¹ := by group
    _ = h * (g * y * g⁻¹) * h⁻¹ := by rw [hgh]

private lemma fzrAux_conjX_conjX {G : Type} [Group G] {X P : Subgroup G} (hXP : X ≤ P)
    (hX : ∀ x : G, x ∈ X ↔ x ∈ P ∧ x * x = 1) (g h : G)
    (hg : ∀ p ∈ P, g * p * g⁻¹ ∈ P) (hh : ∀ p ∈ P, h * p * h⁻¹ ∈ P)
    (hgh : g * h * g⁻¹ = h) (x : X) :
    fzrAux_conjX hXP hX g hg (fzrAux_conjX hXP hX h hh x)
      = fzrAux_conjX hXP hX h hh (fzrAux_conjX hXP hX g hg x) := by
  apply Subtype.ext
  change g * (h * (x : G) * h⁻¹) * g⁻¹ = h * (g * (x : G) * g⁻¹) * h⁻¹
  exact fzrAux_conj_conj hgh

private lemma fzrAux_commMap_conj {H : Type} [CommGroup H] (A B : H →* H)
    (hAB : ∀ x, A (B x) = B (A x)) (x : H) :
    fzrAux_commMap A (B x) = B (fzrAux_commMap A x) := by
  simp only [fzrAux_commMap_apply, hAB x, map_mul, map_inv]

private lemma fzrAux_comm_t_Z {G : Type} [Group G] {t tau lam rho : G}
    {Z E W Q R T : Subgroup G} (h : FzStr t tau lam rho Z E W Q R T) {z : G}
    (hz : z ∈ Z) : t * z * t⁻¹ = z := by
  have hzW : z ∈ W := h.EW (h.ZE hz)
  have hcomm : t * z = z * t := h.W_comm t h.t_mem z hzW
  rw [hcomm]; group

private lemma fzrAux_t_comm_mem_Z {G : Type} [Group G] {t tau lam rho : G}
    {Z E W Q R T : Subgroup G} (h : FzStr t tau lam rho Z E W Q R T) {x : G}
    (hxT : x ∈ T) : t * x * t⁻¹ * x⁻¹ ∈ Z := by
  obtain ⟨z, hz, hz'⟩ := h.T_t x hxT
  have htz : t * z * t⁻¹ = z := fzrAux_comm_t_Z h hz
  have hxz : x * t * x⁻¹ * t⁻¹ = z := by rw [hz', htz]
  have : t * x * t⁻¹ * x⁻¹ = z⁻¹ := by
    have hmain : (t * x * t⁻¹ * x⁻¹) * (x * t * x⁻¹ * t⁻¹) = 1 := by group
    rw [hxz] at hmain
    exact eq_inv_of_mul_eq_one_left hmain
  rw [this]
  exact Z.inv_mem hz

private lemma fzrAux_tau_comm_mem_Z {G : Type} [Group G] {t tau lam rho : G}
    {Z E W Q R T P : Subgroup G} (h : FzStr t tau lam rho Z E W Q R T)
    (hP : FzPFacts t tau rho E W Q T P) {X : Subgroup G} (hXP : X ≤ P)
    (hX : ∀ x : G, x ∈ X ↔ x ∈ P ∧ x * x = 1) {x : G} (hx : x ∈ X) :
    tau * x * tau⁻¹ * x⁻¹ ∈ Z := by
  have htauT : tau ∈ T := h.RT h.tau_R
  have hxP : x ∈ P := hXP hx
  have hcx : tau * x * tau⁻¹ * x⁻¹ ∈ X :=
    X.mul_mem (fzrAux_conj_mem hXP hX (hP.nrm_P tau htauT) hx) (X.inv_mem hx)
  have hW : tau * x * tau⁻¹ * x⁻¹ ∈ W := by
    have hq := h.tau_Q x (hP.PQ hxP)
    rwa [commutatorElement_def] at hq
  have hE : tau * x * tau⁻¹ * x⁻¹ ∈ E := hP.PW _ (hXP hcx) hW
  have hsq : (tau * x * tau⁻¹ * x⁻¹) * (tau * x * tau⁻¹ * x⁻¹) = 1 :=
    ((hX _).mp hcx).2
  exact h.E_invol _ hE (by rw [pow_two]; exact hsq)

theorem fzr_B_cent {G : Type} [Group G] [Finite G] {t tau lam rho : G}
    {Z E W Q R T P X : Subgroup G} (h : FzStr t tau lam rho Z E W Q R T)
    (hP : FzPFacts t tau rho E W Q T P) (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hXP : X ≤ P) (hX : ∀ x : G, x ∈ X ↔ x ∈ P ∧ x * x = 1) (hX16 : Nat.card X = 16) :
    ∃ s : G, (s = tau ∨ s = t * tau) ∧ ∀ x ∈ X, s * x = x * s := by
  have hPT : P ≤ T := hP.PQ.trans (h.QR.trans h.RT)
  have htT : t ∈ T := h.RT (h.QR (h.WQ h.t_mem))
  have htauT : tau ∈ T := h.RT h.tau_R
  have hlamT : lam ∈ T := h.lam_T
  have ht2 : t * t = 1 := by rw [← pow_two]; exact h.t_sq
  have hZX : Z ≤ X := by
    intro z hz
    rw [hX]
    exact ⟨hP.EP (h.ZE hz), by rw [← pow_two]; exact h.Z_sq z hz⟩
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x :=
    fun x hx y hy => hPc x (hXP hx) y (hXP hy)
  letI : CommGroup X :=
    { (inferInstance : Group X) with mul_comm := fun a b => Subtype.ext (hXc a a.2 b b.2) }
  have hX2 : ∀ x : X, x * x = 1 := by
    intro x
    apply Subtype.ext
    simpa using ((hX (x : G)).mp x.2).2
  let A_t : X →* X := fzrAux_conjX hXP hX t (hP.nrm_P t htT)
  let A_tau : X →* X := fzrAux_conjX hXP hX tau (hP.nrm_P tau htauT)
  let A_rho : X →* X := fzrAux_conjX hXP hX rho hP.nrm_P_rho
  let A_lam : X →* X := fzrAux_conjX hXP hX lam (hP.nrm_P lam hlamT)
  let c : X →* X := fzrAux_commMap A_t
  let d : X →* X := fzrAux_commMap A_tau
  have hA_t_apply : ∀ x : X, ((A_t x : X) : G) = t * (x : G) * t⁻¹ := fun x => rfl
  have hA_tau_apply : ∀ x : X, ((A_tau x : X) : G) = tau * (x : G) * tau⁻¹ := fun x => rfl
  have hA_rho_apply : ∀ x : X, ((A_rho x : X) : G) = rho * (x : G) * rho⁻¹ := fun x => rfl
  have hA_lam_apply : ∀ x : X, ((A_lam x : X) : G) = lam * (x : G) * lam⁻¹ := fun x => rfl
  have hc_apply : ∀ x : X, ((c x : X) : G) = t * (x : G) * t⁻¹ * (x : G)⁻¹ := fun x => rfl
  have hd_apply : ∀ x : X, ((d x : X) : G) = tau * (x : G) * tau⁻¹ * (x : G)⁻¹ := fun x => rfl
  let Z' : Subgroup X := Z.subgroupOf X
  have hZ'4 : Nat.card Z' = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZX).toEquiv]
    exact h.card_Z
  have hA_rho3 : ∀ x : X, A_rho (A_rho (A_rho x)) = x := by
    intro x
    apply Subtype.ext
    rw [hA_rho_apply, hA_rho_apply, hA_rho_apply]
    have h3 : rho * rho * rho = 1 := by
      have h' := h.rho_ord
      rw [pow_succ, pow_succ] at h'
      simpa using h'
    calc rho * (rho * (rho * (x : G) * rho⁻¹) * rho⁻¹) * rho⁻¹
        = (rho * rho * rho) * (x : G) * (rho * rho * rho)⁻¹ := by group
      _ = (x : G) := by rw [h3]; group
  have hA_lam2 : ∀ x : X, A_lam (A_lam x) = x := by
    intro x
    apply Subtype.ext
    rw [hA_lam_apply, hA_lam_apply]
    have h2 : lam * lam = 1 := by simpa [pow_two] using h.lam_sq
    calc lam * (lam * (x : G) * lam⁻¹) * lam⁻¹
        = (lam * lam) * (x : G) * (lam * lam)⁻¹ := by group
      _ = (x : G) := by rw [h2]; group
  have hA_lam_rho : ∀ x : X, A_lam (A_rho (A_lam x)) = A_rho (A_rho x) := by
    intro x
    apply Subtype.ext
    simp only [hA_lam_apply, hA_rho_apply]
    have h3 : rho * rho * rho = 1 := by
      have h' := h.rho_ord
      rw [pow_succ, pow_succ] at h'
      simpa using h'
    have hrinv2 : (rho * rho)⁻¹ = rho := inv_eq_of_mul_eq_one_right h3
    have hrinv : rho⁻¹ = rho * rho := by
      have h2 := congrArg Inv.inv hrinv2
      simpa using h2.symm
    have hlinv : lam * rho⁻¹ * lam⁻¹ = rho := by
      have h2 := congrArg Inv.inv h.lam_rho
      simpa [mul_inv_rev, mul_assoc] using h2
    have hmid : lam * (lam * (x : G) * lam⁻¹) * lam⁻¹ = (x : G) := by
      have h2 : lam * lam = 1 := by simpa [pow_two] using h.lam_sq
      calc lam * (lam * (x : G) * lam⁻¹) * lam⁻¹
          = (lam * lam) * (x : G) * (lam * lam)⁻¹ := by group
        _ = (x : G) := by rw [h2]; group
    have hL : rho⁻¹ * (x : G) * rho = (rho * rho) * (x : G) * (rho * rho)⁻¹ := by
      rw [hrinv2, hrinv]
    have hLr : rho * (rho * (x : G) * rho⁻¹) * rho⁻¹
        = (rho * rho) * (x : G) * (rho * rho)⁻¹ := by group
    calc lam * (rho * (lam * (x : G) * lam⁻¹) * rho⁻¹) * lam⁻¹
        = (lam * rho * lam⁻¹) * (lam * (lam * (x : G) * lam⁻¹) * lam⁻¹)
            * (lam * rho⁻¹ * lam⁻¹) := by group
      _ = rho⁻¹ * (x : G) * rho := by rw [h.lam_rho, hlinv, hmid]
      _ = rho * (rho * (x : G) * rho⁻¹) * rho⁻¹ := by rw [hL, hLr]
  have hfpf : ∀ x : X, A_rho x = x → x = 1 := by
    intro x hx
    apply Subtype.ext
    have hx' : rho * (x : G) * rho⁻¹ = (x : G) := by
      have := congrArg (fun w : X => (w : G)) hx
      rwa [hA_rho_apply] at this
    exact hP.rho_fpf (x : G) (hXP x.2) hx'
  have hρZ : ∀ z ∈ Z', A_rho z ∈ Z' := by
    intro z hz
    change rho * (z : G) * rho⁻¹ ∈ Z
    exact h.rho_nrm_Z (z : G) hz
  have hlZ : ∀ z ∈ Z', A_lam z ∈ Z' := by
    intro z hz
    change lam * (z : G) * lam⁻¹ ∈ Z
    exact h.nrm_Z lam h.lam_T (z : G) hz
  have hlmove : ∃ z ∈ Z', A_lam z ≠ z := by
    obtain ⟨z, hz, hz'⟩ := h.lam_Z
    refine ⟨⟨z, hZX hz⟩, hz, ?_⟩
    intro hcon
    exact hz' (by
      have := congrArg (fun w : X => (w : G)) hcon
      change lam * z * lam⁻¹ = z at this
      exact this)
  have hcZ : ∀ x : X, c x ∈ Z' := by
    intro x
    change t * (x : G) * t⁻¹ * (x : G)⁻¹ ∈ Z
    exact fzrAux_t_comm_mem_Z h (hPT (hXP x.2))
  have hdZ : ∀ x : X, d x ∈ Z' := by
    intro x
    change tau * (x : G) * tau⁻¹ * (x : G)⁻¹ ∈ Z
    exact fzrAux_tau_comm_mem_Z h hP hXP hX x.2
  have hc0 : ∀ z ∈ Z', c z = 1 := by
    intro z hz
    apply Subtype.ext
    change t * (z : G) * t⁻¹ * (z : G)⁻¹ = 1
    rw [fzrAux_comm_t_Z (z := (z : G)) h hz]
    group
  have hd0 : ∀ z ∈ Z', d z = 1 := by
    intro z hz
    apply Subtype.ext
    change tau * (z : G) * tau⁻¹ * (z : G)⁻¹ = 1
    have hzW : (z : G) ∈ W := h.EW (h.ZE hz)
    have hz2 : (z : G) * (z : G) = 1 := by rw [← pow_two]; exact h.Z_sq (z : G) hz
    rw [h.tau_W (z : G) hzW]
    have := congrArg Inv.inv hz2
    simpa [mul_inv_rev] using this
  have ht_rho : t * rho * t⁻¹ = rho := by
    have h' : rho * t = t * rho := by
      have h2 := congrArg (fun y => y * rho) h.rho_t
      simpa [mul_assoc] using h2
    rw [← h']; group
  have ht_lam : t * lam * t⁻¹ = lam := by
    have h' : lam * t = t * lam := by
      have h2 := congrArg (fun y => y * lam) h.lam_t
      simpa [mul_assoc] using h2
    rw [← h']; group
  have htau_rho : tau * rho * tau⁻¹ = rho := by rw [h.tau_rho]; group
  have htau_lam : tau * lam * tau⁻¹ = lam := by rw [h.tau_lam]; group
  have hAB_tr : ∀ x : X, A_t (A_rho x) = A_rho (A_t x) :=
    fun x => fzrAux_conjX_conjX hXP hX t rho (hP.nrm_P t htT) hP.nrm_P_rho ht_rho x
  have hAB_tl : ∀ x : X, A_t (A_lam x) = A_lam (A_t x) :=
    fun x => fzrAux_conjX_conjX hXP hX t lam (hP.nrm_P t htT)
      (hP.nrm_P lam hlamT) ht_lam x
  have hAB_taurho : ∀ x : X, A_tau (A_rho x) = A_rho (A_tau x) :=
    fun x => fzrAux_conjX_conjX hXP hX tau rho (hP.nrm_P tau htauT) hP.nrm_P_rho
      htau_rho x
  have hAB_taulam : ∀ x : X, A_tau (A_lam x) = A_lam (A_tau x) :=
    fun x => fzrAux_conjX_conjX hXP hX tau lam (hP.nrm_P tau htauT)
      (hP.nrm_P lam hlamT) htau_lam x
  have hcρ : ∀ x : X, c (A_rho x) = A_rho (c x) :=
    fun x => fzrAux_commMap_conj A_t A_rho hAB_tr x
  have hdρ : ∀ x : X, d (A_rho x) = A_rho (d x) :=
    fun x => fzrAux_commMap_conj A_tau A_rho hAB_taurho x
  have hcl : ∀ x : X, c (A_lam x) = A_lam (c x) :=
    fun x => fzrAux_commMap_conj A_t A_lam hAB_tl x
  have hdl : ∀ x : X, d (A_lam x) = A_lam (d x) :=
    fun x => fzrAux_commMap_conj A_tau A_lam hAB_taulam x
  have hc : ∃ x : X, c x ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hXleZ : X ≤ Z := by
      intro x hx
      have hcx : c ⟨x, hx⟩ = 1 := hcon ⟨x, hx⟩
      have hG : t * x * t⁻¹ * x⁻¹ = 1 := by
        have := congrArg (fun w : X => (w : G)) hcx
        rwa [hc_apply] at this
      have hxt : x * t * x⁻¹ = t := by
        have hinv : x * t * x⁻¹ * t⁻¹ = 1 := by
          have := congrArg Inv.inv hG
          simpa [mul_inv_rev, mul_assoc] using this
        exact mul_inv_eq_one.mp hinv
      have hxQ : x ∈ Q := hP.PQ (hXP hx)
      have hxW : x ∈ W := by
        by_contra hxW
        exact h.Q_t x hxQ hxW hxt
      have hxE : x ∈ E := hP.PW x (hXP hx) hxW
      exact h.E_invol x hxE (by rw [pow_two]; exact ((hX x).mp hx).2)
    have hcard := Subgroup.card_le_of_le hXleZ
    rw [hX16, h.card_Z] at hcard
    omega
  rcases fzr_B_core (X := X) hX2 hX16 hZ'4 A_rho A_lam hA_rho3 hA_lam2 hA_lam_rho hfpf
      hρZ hlZ hlmove c d hcZ hdZ hc0 hd0 hcρ hdρ hcl hdl hc with hd1 | hdc
  · refine ⟨tau, Or.inl rfl, ?_⟩
    intro x hx
    have h1 : d ⟨x, hx⟩ = 1 := hd1 ⟨x, hx⟩
    have hG : tau * x * tau⁻¹ = x := by
      have := congrArg (fun w : X => (w : G)) h1
      rw [hd_apply] at this
      exact mul_inv_eq_one.mp this
    have : tau * x = x * tau := by
      have h2 := congrArg (fun y => y * tau) hG
      simpa [mul_assoc] using h2
    exact this
  · refine ⟨t * tau, Or.inr rfl, ?_⟩
    intro x hx
    have h1 : d ⟨x, hx⟩ = c ⟨x, hx⟩ := hdc ⟨x, hx⟩
    have hG : tau * x * tau⁻¹ = t * x * t⁻¹ := by
      have := congrArg (fun w : X => (w : G)) h1
      rw [hd_apply, hc_apply] at this
      exact mul_right_cancel this
    have hG2 : (t * tau) * x * (t * tau)⁻¹ = x := by
      calc (t * tau) * x * (t * tau)⁻¹ = t * (tau * x * tau⁻¹) * t⁻¹ := by group
        _ = t * (t * x * t⁻¹) * t⁻¹ := by rw [hG]
        _ = x := by
              calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
                _ = x := by rw [ht2]; group
    have : (t * tau) * x = x * (t * tau) := by
      have h3 := congrArg (fun y => y * (t * tau)) hG2
      simpa [mul_assoc] using h3
    exact this

end CFSG.OddStandard.SmallF3.FritzII
