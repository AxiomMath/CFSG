module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL49H

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma t_mem_ctxX (t tau x₁ x₂ : G) : t ∈ ctxX t tau x₁ x₂ := by
  rw [ctxX]
  exact Subgroup.subset_closure (by simp)

private lemma t_mem_ctxE (t x₁ x₂ : G) : t ∈ ctxE t x₁ x₂ := by
  rw [ctxE]
  exact Subgroup.subset_closure (by simp)

private lemma y_mem_ctxE (t x₁ x₂ : G) : x₁ ^ 2 ∈ ctxE t x₁ x₂ := by
  rw [ctxE]
  exact Subgroup.subset_closure (by simp)

private lemma z_mem_ctxE (t x₁ x₂ : G) : (x₁ * x₂) ^ 2 ∈ ctxE t x₁ x₂ := by
  rw [ctxE]
  exact Subgroup.subset_closure (by simp)

private lemma t_commute_tau (h : Ctx t L S x₁ x₂ lam rho tau) : Commute t tau :=
  (mem_invCent_iff.mp (h.le_invCent h.tau_mem)).symm

private lemma commute_ty (h : Ctx0 t L S x₁ x₂ lam rho) : Commute t (x₁ ^ 2) :=
  (mem_invCent_iff.mp (L_le_invCent h.hyp (y_z_mem_L h).1)).symm

private lemma commute_tz (h : Ctx0 t L S x₁ x₂ lam rho) : Commute t ((x₁ * x₂) ^ 2) :=
  (mem_invCent_iff.mp (L_le_invCent h.hyp (y_z_mem_L h).2)).symm

private lemma mem_zpowers_eq_one_or_eq {z g : G} (hz : z * z = 1) (hg : g ∈ zpowers z) :
    g = 1 ∨ g = z := by
  let H : Subgroup G :=
    { carrier := {g : G | g = 1 ∨ g = z}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (rfl | rfl) (rfl | rfl)
        · exact Or.inl (by simp)
        · exact Or.inr (by simp)
        · exact Or.inr (by simp)
        · exact Or.inl (by rw [hz])
      inv_mem' := by
        rintro a (rfl | rfl)
        · exact Or.inl (by simp)
        · exact Or.inr (by rw [inv_eq_of_mul_eq_one_right hz]) }
  exact (Subgroup.zpowers_le.mpr (show z ∈ H from Or.inr rfl)) hg

private lemma ctxX_le_sup (t tau x₁ x₂ : G) :
    ctxX t tau x₁ x₂ ≤ ctxE t x₁ x₂ ⊔ zpowers tau := by
  rw [ctxX]
  refine (Subgroup.closure_le (K := ctxE t x₁ x₂ ⊔ zpowers tau)).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with h | h | h | h
  · rw [h]; exact Subgroup.mem_sup_left (t_mem_ctxE t x₁ x₂)
  · rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers tau)
  · rw [h]; exact Subgroup.mem_sup_left (y_mem_ctxE t x₁ x₂)
  · rw [h]; exact Subgroup.mem_sup_left (z_mem_ctxE t x₁ x₂)

private lemma ctxE_le_fourGrp_sup_zpowers_t (t x₁ x₂ : G) :
    ctxE t x₁ x₂ ≤ fourGrp x₁ x₂ ⊔ zpowers t := by
  rw [ctxE]
  refine (Subgroup.closure_le (K := fourGrp x₁ x₂ ⊔ zpowers t)).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with h | h | h
  · rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  · rw [h]; exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  · rw [h]; exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))

private lemma commute_fourGrp_t (h : Ctx t L S x₁ x₂ lam rho tau) :
    ∀ f ∈ fourGrp x₁ x₂, Commute f t := by
  intro f hf
  rw [fourGrp] at hf
  induction hf using Subgroup.closure_induction with
  | mem a ha =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact (commute_ty h.toCtx0).symm
      · exact (commute_tz h.toCtx0).symm
  | one => exact Commute.one_left t
  | mul x y hx hy ihx ihy => exact ihx.mul_left ihy
  | inv x hx ihx => exact ihx.inv_left

private lemma commute_fourGrp_tau (h : Ctx t L S x₁ x₂ lam rho tau) :
    ∀ f ∈ fourGrp x₁ x₂, Commute f tau := by
  intro f hf
  rw [fourGrp] at hf
  induction hf using Subgroup.closure_induction with
  | mem a ha =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact (tau_commute_y h).symm
      · exact (tau_commute_z h).symm
  | one => exact Commute.one_left tau
  | mul x y hx hy ihx ihy => exact ihx.mul_left ihy
  | inv x hx ihx => exact ihx.inv_left

private lemma commute_ctxE_tau (h : Ctx t L S x₁ x₂ lam rho tau) :
    ∀ e ∈ ctxE t x₁ x₂, Commute e tau := by
  intro e he
  rw [ctxE] at he
  induction he using Subgroup.closure_induction with
  | mem a ha =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · exact t_commute_tau h
      · exact (tau_commute_y h).symm
      · exact (tau_commute_z h).symm
  | one => exact Commute.one_left tau
  | mul x y hx hy ihx ihy => exact ihx.mul_left ihy
  | inv x hx ihx => exact ihx.inv_left

private lemma fourGrp_commute_zpowers_t (h : Ctx t L S x₁ x₂ lam rho tau) :
    ∀ a ∈ fourGrp x₁ x₂, ∀ b ∈ zpowers t, a * b = b * a := by
  intro a ha b hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (commute_fourGrp_t h a ha).zpow_right k

private lemma fourGrp_commute_zpowers_tau (h : Ctx t L S x₁ x₂ lam rho tau) :
    ∀ a ∈ fourGrp x₁ x₂, ∀ b ∈ zpowers tau, a * b = b * a := by
  intro a ha b hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (commute_fourGrp_tau h a ha).zpow_right k

private lemma conj_tau_eq_sq_mul_tau {a : G} (ha : tau * a * tau⁻¹ = a⁻¹) :
    a * tau * a⁻¹ = a ^ 2 * tau := by
  calc a * tau * a⁻¹
      = a * (tau * a⁻¹ * tau⁻¹) * tau := by group
    _ = a * (tau * a * tau⁻¹)⁻¹ * tau := by
          rw [show tau * a⁻¹ * tau⁻¹ = (tau * a * tau⁻¹)⁻¹ by group]
    _ = a * (a⁻¹)⁻¹ * tau := by rw [ha]
    _ = a ^ 2 * tau := by rw [inv_inv, pow_two]

private lemma tau_conj_x1x2 (h : Ctx t L S x₁ x₂ lam rho tau) :
    tau * (x₁ * x₂) * tau⁻¹ = (x₁ * x₂)⁻¹ := by
  have hcomm : Commute x₁ x₂ := h.wreath.comm
  calc tau * (x₁ * x₂) * tau⁻¹
      = (tau * x₁ * tau⁻¹) * (tau * x₂ * tau⁻¹) := by group
    _ = x₁⁻¹ * x₂⁻¹ := by rw [h.tau_x₁, h.tau_x₂]
    _ = (x₂ * x₁)⁻¹ := by rw [mul_inv_rev]
    _ = (x₁ * x₂)⁻¹ := by rw [hcomm.eq]

private lemma conjIn_pair_of {M : Subgroup G} {m f : G} (hm : m ∈ M) (hmH : m ∈ invCent t)
    (hconj : m * tau * m⁻¹ = tau * f) :
    tau * f ∈ conjIn M tau ∧ t * tau * f ∈ conjIn M (t * tau) := by
  have hcommt : m * t = t * m := mem_invCent_iff.mp hmH
  have h2 : m * (t * tau) * m⁻¹ = t * tau * f := by
    calc m * (t * tau) * m⁻¹
        = (m * t) * tau * m⁻¹ := by group
      _ = (t * m) * tau * m⁻¹ := by rw [hcommt]
      _ = t * (m * tau * m⁻¹) := by group
      _ = t * (tau * f) := by rw [hconj]
      _ = t * tau * f := by group
  exact ⟨⟨m, hm, hconj⟩, ⟨m, hm, h2⟩⟩

private lemma conjIn_eq_of_mem {K : Subgroup G} {a u : G} (hu : u ∈ conjIn K a) :
    conjIn K u = conjIn K a := by
  obtain ⟨m, hm, hmu⟩ := hu
  ext v
  constructor
  · rintro ⟨k, hk, hkv⟩
    refine ⟨k * m, K.mul_mem hk hm, ?_⟩
    calc (k * m) * a * (k * m)⁻¹
        = k * (m * a * m⁻¹) * k⁻¹ := by group
      _ = k * u * k⁻¹ := by rw [hmu]
      _ = v := hkv
  · rintro ⟨k, hk, hka⟩
    refine ⟨k * m⁻¹, K.mul_mem hk (K.inv_mem hm), ?_⟩
    have ha : m⁻¹ * u * m = a := by rw [← hmu]; group
    calc (k * m⁻¹) * u * (k * m⁻¹)⁻¹
        = k * (m⁻¹ * u * m) * k⁻¹ := by group
      _ = k * a * k⁻¹ := by rw [ha]
      _ = v := hka

theorem conjIn_ctxM_subset_ctxX (t tau x₁ x₂ : G) :
    conjIn (ctxM t tau x₁ x₂) t ⊆ (ctxX t tau x₁ x₂ : Set G) := by
  rintro u ⟨m, hm, rfl⟩
  rw [ctxM, Subgroup.mem_set_normalizer_iff] at hm
  exact (hm t).mp (t_mem_ctxX t tau x₁ x₂)

theorem mem_ctxX_cases (h : Ctx t L S x₁ x₂ lam rho tau) (h44 : tau ^ 2 = 1) {u : G}
    (hu : u ∈ ctxX t tau x₁ x₂) :
    u ∈ (fourGrp x₁ x₂ : Set G) ∨ u ∈ t • (fourGrp x₁ x₂ : Set G) ∨
      u ∈ tau • (fourGrp x₁ x₂ : Set G) ∨ u ∈ (t * tau) • (fourGrp x₁ x₂ : Set G) := by
  have hE_comm_tau : ∀ e ∈ ctxE t x₁ x₂, ∀ s ∈ zpowers tau, e * s = s * e := by
    intro e he s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    exact (commute_ctxE_tau h e he).zpow_right k
  have hu' : u ∈ ctxE t x₁ x₂ ⊔ zpowers tau := ctxX_le_sup t tau x₁ x₂ hu
  obtain ⟨e, heE, s, hsZ, hue⟩ := (mem_sup_iff_of_commute hE_comm_tau).mp hu'
  have hs_cases : s = 1 ∨ s = tau :=
    mem_zpowers_eq_one_or_eq (z := tau) (by rw [← pow_two]; exact h44) hsZ
  have he' : e ∈ fourGrp x₁ x₂ ⊔ zpowers t := ctxE_le_fourGrp_sup_zpowers_t t x₁ x₂ heE
  obtain ⟨f, hfF, q, hqZ, heq⟩ :=
    (mem_sup_iff_of_commute (fourGrp_commute_zpowers_t h)).mp he'
  have hq_cases : q = 1 ∨ q = t :=
    mem_zpowers_eq_one_or_eq (z := t) (t_mul_self h.hyp) hqZ
  have hfq : f * q = q * f := fourGrp_commute_zpowers_t h f hfF q hqZ
  have hfs : f * s = s * f := fourGrp_commute_zpowers_tau h f hfF s hsZ
  have hu_eq : u = (q * s) * f := by
    rw [hue, heq]
    calc (f * q) * s = (q * f) * s := by rw [hfq]
      _ = q * (f * s) := by group
      _ = q * (s * f) := by rw [hfs]
      _ = (q * s) * f := by group
  rcases hs_cases with rfl | rfl <;> rcases hq_cases with rfl | rfl
  · left
    rw [hu_eq]
    simpa using hfF
  · right; left
    rw [Set.mem_smul_set]
    exact ⟨f, hfF, by rw [hu_eq]; simp [smul_eq_mul]⟩
  · right; right; left
    rw [Set.mem_smul_set]
    exact ⟨f, hfF, by rw [hu_eq]; simp [smul_eq_mul]⟩
  · right; right; right
    rw [Set.mem_smul_set]
    exact ⟨f, hfF, by rw [hu_eq]; simp [smul_eq_mul]⟩

theorem tau_mul_mem_conjIn (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) {f : G} (hf : f ∈ fourGrp x₁ x₂) :
    tau * f ∈ conjIn (ctxM t tau x₁ x₂) tau ∧
      t * tau * f ∈ conjIn (ctxM t tau x₁ x₂) (t * tau) := by
  have hnorm := normalizer_X_of h h43 h44
  have hx1W : x₁ ∈ ctxW t x₁ x₂ :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hx2W : x₂ ∈ ctxW t x₁ x₂ :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hx1inf : x₁ ∈ invCent t ⊓ ctxM t tau x₁ x₂ := by
    rw [hnorm]; exact Subgroup.mem_sup_left hx1W
  have hx2inf : x₂ ∈ invCent t ⊓ ctxM t tau x₁ x₂ := by
    rw [hnorm]; exact Subgroup.mem_sup_left hx2W
  have hx1M : x₁ ∈ ctxM t tau x₁ x₂ := hx1inf.2
  have hx2M : x₂ ∈ ctxM t tau x₁ x₂ := hx2inf.2
  have hx1H : x₁ ∈ invCent t := hx1inf.1
  have hx2H : x₂ ∈ invCent t := hx2inf.1
  have hf_cases := mem_closure_pair_cases (a := x₁ ^ 2) (b := (x₁ * x₂) ^ 2)
    (y_commute_z h.wreath) (y_mul_self_ne_one h.wreath).1
    (z_mul_self_ne_one h.toCtx0).1 hf
  rcases hf_cases with hf1 | hf1 | hf1 | hf1
  · rw [hf1]
    exact conjIn_pair_of (M := ctxM t tau x₁ x₂) (m := 1) (f := 1)
      (Subgroup.one_mem _) (Subgroup.one_mem _) (by simp)
  · rw [hf1]
    exact conjIn_pair_of (M := ctxM t tau x₁ x₂) (m := x₁) (f := x₁ ^ 2)
      hx1M hx1H (by rw [conj_tau_eq_sq_mul_tau h.tau_x₁, tau_commute_y h])
  · rw [hf1]
    exact conjIn_pair_of (M := ctxM t tau x₁ x₂) (m := x₁ * x₂) (f := (x₁ * x₂) ^ 2)
      ((ctxM t tau x₁ x₂).mul_mem hx1M hx2M) ((invCent t).mul_mem hx1H hx2H)
      (by rw [conj_tau_eq_sq_mul_tau (tau_conj_x1x2 h), tau_commute_z h])
  · rw [hf1]
    exact conjIn_pair_of (M := ctxM t tau x₁ x₂) (m := x₂) (f := x₁ ^ 2 * (x₁ * x₂) ^ 2)
      hx2M hx2H (by
        rw [conj_tau_eq_sq_mul_tau h.tau_x₂, h.wreath.x₂_sq]
        exact ((show Commute tau (x₁ ^ 2) from tau_commute_y h).mul_right
          (show Commute tau ((x₁ * x₂) ^ 2) from tau_commute_z h)).eq.symm)

theorem tM_cases_of (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) (h2 : 2 ∣ S.index)
    (hS1 : ∀ 𝒮 : Sylow 2 G, S < (𝒮 : Subgroup G) →
      ctxS1 S (𝒮 : Subgroup G) ≤ ctxM t tau x₁ x₂) :
    conjIn (ctxM t tau x₁ x₂) t = t • (fourGrp x₁ x₂ : Set G) ∨
      conjIn (ctxM t tau x₁ x₂) t =
        t • (fourGrp x₁ x₂ : Set G) ∪ tau • (fourGrp x₁ x₂ : Set G) ∨
      conjIn (ctxM t tau x₁ x₂) t =
        t • (fourGrp x₁ x₂ : Set G) ∪ (t * tau) • (fourGrp x₁ x₂ : Set G) ∨
      conjIn (ctxM t tau x₁ x₂) t =
        t • (fourGrp x₁ x₂ : Set G) ∪ tau • (fourGrp x₁ x₂ : Set G) ∪
          (t * tau) • (fourGrp x₁ x₂ : Set G) := by
  let M : Subgroup G := ctxM t tau x₁ x₂
  let F : Set G := (fourGrp x₁ x₂ : Set G)
  let Tt : Set G := conjIn M t
  change Tt = t • F ∨ Tt = t • F ∪ tau • F ∨ Tt = t • F ∪ (t * tau) • F ∨
    Tt = t • F ∪ tau • F ∪ (t * tau) • F
  have htF : t • F ⊆ Tt := by
    intro u hu
    rw [Set.mem_smul_set] at hu
    obtain ⟨f, hf, hfu⟩ := hu
    rw [← hfu]
    simpa [F, smul_eq_mul] using tF_subset_conjIn h h43 h44 h2 hS1 f hf
  have hdisjF : ∀ u, u ∈ Tt → u ∈ F → False := by
    intro u hu hF
    change u ∈ conjIn (ctxM t tau x₁ x₂) t at hu
    obtain ⟨m, hm, hmu⟩ := hu
    exact (tG_inf_four_of_ctx h m u hF) hmu
  have hXsub : ∀ u, u ∈ Tt → u ∈ (ctxX t tau x₁ x₂ : Set G) := by
    intro u hu
    exact conjIn_ctxM_subset_ctxX t tau x₁ x₂ hu
  have hsub : Tt ⊆ t • F ∪ tau • F ∪ (t * tau) • F := by
    intro u hu
    rcases mem_ctxX_cases h h44 (hXsub u hu) with hF | htF | htauF | httauF
    · exact (hdisjF u hu hF).elim
    · exact Or.inl (Or.inl htF)
    · exact Or.inl (Or.inr htauF)
    · exact Or.inr httauF
  have htau_sub : tau ∈ Tt → tau • F ⊆ Tt := by
    intro htau u hu
    rw [Set.mem_smul_set] at hu
    obtain ⟨f, hf, hfu⟩ := hu
    have h1 : tau * f ∈ conjIn M tau := (tau_mul_mem_conjIn h h43 h44 hf).1
    have heq : conjIn M tau = Tt := conjIn_eq_of_mem (K := M) (a := t) (u := tau) htau
    rw [heq] at h1
    rw [← hfu]
    simpa [smul_eq_mul] using h1
  have httau_sub : t * tau ∈ Tt → (t * tau) • F ⊆ Tt := by
    intro httau u hu
    rw [Set.mem_smul_set] at hu
    obtain ⟨f, hf, hfu⟩ := hu
    have h1 : t * tau * f ∈ conjIn M (t * tau) := (tau_mul_mem_conjIn h h43 h44 hf).2
    have heq : conjIn M (t * tau) = Tt := conjIn_eq_of_mem (K := M) (a := t) (u := t * tau) httau
    rw [heq] at h1
    rw [← hfu]
    simpa [smul_eq_mul] using h1
  have htau_disj : tau ∉ Tt → ∀ u, u ∈ tau • F → u ∈ Tt → False := by
    intro htau u hu1 hu2
    rw [Set.mem_smul_set] at hu1
    obtain ⟨f, hf, hfu⟩ := hu1
    have hmem : tau * f ∈ conjIn M tau := (tau_mul_mem_conjIn h h43 h44 hf).1
    have htf : tau * f ∈ Tt := by
      rw [show tau * f = u by simpa [smul_eq_mul] using hfu]
      exact hu2
    have heq : conjIn M (tau * f) = Tt :=
      conjIn_eq_of_mem (K := M) (a := t) (u := tau * f) htf
    have htau_in : tau ∈ conjIn M (tau * f) := by
      rw [conjIn_eq_of_mem (K := M) (a := tau) (u := tau * f) hmem]
      exact ⟨1, Subgroup.one_mem _, by simp⟩
    rw [heq] at htau_in
    exact htau htau_in
  have httau_disj : t * tau ∉ Tt → ∀ u, u ∈ (t * tau) • F → u ∈ Tt → False := by
    intro httau u hu1 hu2
    rw [Set.mem_smul_set] at hu1
    obtain ⟨f, hf, hfu⟩ := hu1
    have hmem : t * tau * f ∈ conjIn M (t * tau) := (tau_mul_mem_conjIn h h43 h44 hf).2
    have htf : t * tau * f ∈ Tt := by
      rw [show t * tau * f = u by simpa [smul_eq_mul] using hfu]
      exact hu2
    have heq : conjIn M (t * tau * f) = Tt :=
      conjIn_eq_of_mem (K := M) (a := t) (u := t * tau * f) htf
    have hx_in : t * tau ∈ conjIn M (t * tau * f) := by
      rw [conjIn_eq_of_mem (K := M) (a := t * tau) (u := t * tau * f) hmem]
      exact ⟨1, Subgroup.one_mem _, by simp⟩
    rw [heq] at hx_in
    exact httau hx_in
  by_cases htau : tau ∈ Tt
  · by_cases httau : t * tau ∈ Tt
    · right; right; right
      apply le_antisymm
      · exact hsub
      · exact Set.union_subset (Set.union_subset htF (htau_sub htau)) (httau_sub httau)
    · right; left
      apply le_antisymm
      · intro u hu
        rcases hsub hu with h | h
        · rcases h with h1 | h2
          · exact Or.inl h1
          · exact Or.inr h2
        · exact (httau_disj httau u h hu).elim
      · exact Set.union_subset htF (htau_sub htau)
  · by_cases httau : t * tau ∈ Tt
    · right; right; left
      apply le_antisymm
      · intro u hu
        rcases hsub hu with h | h
        · rcases h with h1 | h2
          · exact Or.inl h1
          · exact (htau_disj htau u h2 hu).elim
        · exact Or.inr h
      · exact Set.union_subset htF (httau_sub httau)
    · left
      apply le_antisymm
      · intro u hu
        rcases hsub hu with h | h
        · rcases h with h1 | h2
          · exact h1
          · exact (htau_disj htau u h2 hu).elim
        · exact (httau_disj httau u h hu).elim
      · exact htF

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
