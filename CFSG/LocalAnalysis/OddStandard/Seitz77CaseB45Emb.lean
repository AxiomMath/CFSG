module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Comp
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Wr

public section

namespace CFSG.OddStandard.Seitz77.CaseB45

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

section Act

@[expose] noncomputable def autQ (H : Subgroup G) (φ : MulAut ↥H) : MulAut (↥H ⧸ center ↥H) :=
  QuotientGroup.congr (center ↥H) (center ↥H) φ
    (Subgroup.characteristic_iff_map_eq.1 inferInstance φ)

@[expose] noncomputable def autQHom (H : Subgroup G) : MulAut ↥H →* MulAut (↥H ⧸ center ↥H) where
  toFun := autQ H
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

@[expose] noncomputable def actQ (H : Subgroup G) :
    ↥(normalizer (H : Set G)) →* MulAut (↥H ⧸ center ↥H) :=
  (autQHom H).comp H.normalizerMonoidHom

theorem actQ_mk (H : Subgroup G) (n : ↥(normalizer (H : Set G))) (x : ↥H) :
    actQ H n (QuotientGroup.mk x) = QuotientGroup.mk (H.normalizerMonoidHom n x) := rfl

theorem centralizes_of_actQ_eq_one {H : Subgroup G} (hH : ⁅H, H⁆ = H)
    {n : ↥(normalizer (H : Set G))} (h : actQ H n = 1) {x : G} (hx : x ∈ H) :
    (n : G) * x = x * n := by
  set φ : MulAut ↥H := H.normalizerMonoidHom n with hφ
  have hz : ∀ a : ↥H, a⁻¹ * φ a ∈ center ↥H := by
    intro a
    have h1 : actQ H n (QuotientGroup.mk a) = QuotientGroup.mk a := by
      rw [h]
      rfl
    rw [actQ_mk] at h1
    exact QuotientGroup.eq.1 h1.symm
  have htop : (⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆ : Subgroup ↥H) = ⊤ := by
    have e : (⊤ : Subgroup ↥H).map H.subtype = H := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, e]
    exact hH
  have hfix : ∀ a : ↥H, φ a = a * (a⁻¹ * φ a) := fun a => by group
  have hcomm : ∀ a b : ↥H, φ (a * b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ := by
    intro a b
    obtain ⟨za, hza, ea⟩ : ∃ z ∈ center ↥H, φ a = a * z := ⟨_, hz a, hfix a⟩
    obtain ⟨zb, hzb, eb⟩ : ∃ z ∈ center ↥H, φ b = b * z := ⟨_, hz b, hfix b⟩
    have := commutator_mul_central a b za zb (fun g => (Subgroup.mem_center_iff.1 hza g).symm)
      (fun g => (Subgroup.mem_center_iff.1 hzb g).symm)
    calc φ (a * b * a⁻¹ * b⁻¹) = a * za * (b * zb) * (a * za)⁻¹ * (b * zb)⁻¹ := by
          simp only [map_mul, map_inv, ea, eb]
      _ = a * b * a⁻¹ * b⁻¹ := this
  have hall : ∀ a : ↥H, φ a = a := by
    intro a
    have ha : a ∈ (⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆ : Subgroup ↥H) := by
      rw [htop]
      trivial
    rw [Subgroup.commutator_def] at ha
    refine Subgroup.closure_induction (p := fun a _ => φ a = a) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨u, -, v, -, rfl⟩
      simpa [commutatorElement_def] using hcomm u v
    · exact map_one φ
    · intro a b _ _ ha hb
      rw [map_mul, ha, hb]
    · intro a _ ha
      rw [map_inv, ha]
  have := hall ⟨x, hx⟩
  have h2 := congrArg Subtype.val this
  rw [hφ, Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
  simp only at h2
  calc (n : G) * x = (n : G) * x * (n : G)⁻¹ * n := by group
    _ = x * n := by rw [h2]

end Act

section Coset

variable {G₁ G₂ : Subgroup G} {t : G}

theorem CompData.swap_of_not_mem [Finite G] (c : CompData G₁ G₂ t) {n : G}
    (hn : n ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G))
    (h : n ∉ normalizer (G₁ : Set G)) : cs n G₁ = G₂ ∧ cs n G₂ = G₁ := by
  have h1 : cs n G₁ = G₂ := by
    rcases c.comp_perm hn with h1 | h1
    · exact absurd (mem_normalizer_iff_cs.2 h1) h
    · exact h1
  refine ⟨h1, ?_⟩
  have hnt : n * t ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) := mul_mem hn c.t_mem_normalizer
  have h2 : cs n G₂ = cs (n * t) G₁ := by rw [cs_mul, c.cs_t_G₁]
  rcases c.comp_perm hnt with h3 | h3
  · rw [h2, h3]
  · exfalso
    apply c.G₁_ne_G₂
    have : cs n G₂ = cs n G₁ := by rw [h2, h3, h1]
    have h4 : G₂ = G₁ := by
      have := congrArg (cs n⁻¹) this
      rwa [cs_inv_cs, cs_inv_cs] at this
    exact h4.symm

theorem CompData.mem_normalizer₂_of_mem [Finite G] (c : CompData G₁ G₂ t) {n : G}
    (hn : n ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G))
    (h : n ∈ normalizer (G₁ : Set G)) : cs n G₂ = G₂ := by
  have h1 : cs n G₁ = G₁ := mem_normalizer_iff_cs.1 h
  have hnt : n * t ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) := mul_mem hn c.t_mem_normalizer
  have h2 : cs n G₂ = cs (n * t) G₁ := by rw [cs_mul, c.cs_t_G₁]
  rcases c.comp_perm hnt with h3 | h3
  · exfalso
    apply c.G₁_ne_G₂
    have : cs n G₂ = cs n G₁ := by rw [h2, h3, h1]
    have h4 : G₂ = G₁ := by
      have := congrArg (cs n⁻¹) this
      rwa [cs_inv_cs, cs_inv_cs] at this
    exact h4.symm
  · rw [h2, h3]

theorem CompData.mul_t_mem [Finite G] (c : CompData G₁ G₂ t) {n : G}
    (hn : n ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G))
    (h : n ∉ normalizer (G₁ : Set G)) : n * t ∈ normalizer (G₁ : Set G) := by
  rw [mem_normalizer_iff_cs, cs_mul, c.cs_t_G₁]
  exact (c.swap_of_not_mem hn h).2

theorem CompData.t_mul_mem [Finite G] (c : CompData G₁ G₂ t) {n : G}
    (hn : n ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G))
    (h : n ∉ normalizer (G₁ : Set G)) : t * n ∈ normalizer (G₁ : Set G) := by
  rw [mem_normalizer_iff_cs, cs_mul, (c.swap_of_not_mem hn h).1, c.cs_t_G₂]

theorem CompData.conj_t_mem [Finite G] (c : CompData G₁ G₂ t) {n : G}
    (hn : n ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G))
    (h : n ∈ normalizer (G₁ : Set G)) : t⁻¹ * n * t ∈ normalizer (G₁ : Set G) := by
  rw [mem_normalizer_iff_cs, cs_mul, cs_mul, c.cs_t_G₁, c.mem_normalizer₂_of_mem hn h, c.t_inv,
    c.cs_t_G₂]

theorem CompData.t_not_mem (c : CompData G₁ G₂ t) : t ∉ normalizer (G₁ : Set G) := by
  intro h
  apply c.G₁_ne_G₂
  rw [← c.cs_t_G₁]
  exact (mem_normalizer_iff_cs.1 h).symm

end Coset

section Theta

variable {Q : Type} [Group Q]

open Classical in
@[expose] noncomputable def psiT (G₁ : Subgroup G) (Φ : MulAut (↥G₁ ⧸ center ↥G₁) →* Q) (n : G) :
    Q :=
  if h : n ∈ normalizer (G₁ : Set G) then Φ (actQ G₁ ⟨n, h⟩) else 1

theorem psiT_of_mem (G₁ : Subgroup G) (Φ : MulAut (↥G₁ ⧸ center ↥G₁) →* Q) {n : G}
    (h : n ∈ normalizer (G₁ : Set G)) : psiT G₁ Φ n = Φ (actQ G₁ ⟨n, h⟩) := by simp [psiT, h]

theorem psiT_mul (G₁ : Subgroup G) (Φ : MulAut (↥G₁ ⧸ center ↥G₁) →* Q) {n m : G}
    (hn : n ∈ normalizer (G₁ : Set G)) (hm : m ∈ normalizer (G₁ : Set G)) :
    psiT G₁ Φ (n * m) = psiT G₁ Φ n * psiT G₁ Φ m := by
  rw [psiT_of_mem G₁ Φ (mul_mem hn hm), psiT_of_mem G₁ Φ hn, psiT_of_mem G₁ Φ hm, ← map_mul,
    ← map_mul]
  rfl

theorem psiT_one (G₁ : Subgroup G) (Φ : MulAut (↥G₁ ⧸ center ↥G₁) →* Q) :
    psiT G₁ Φ 1 = 1 := by
  rw [psiT_of_mem G₁ Φ (one_mem _)]
  have : (⟨1, one_mem _⟩ : ↥(normalizer (G₁ : Set G))) = 1 := rfl
  rw [this, map_one, map_one]

open Classical in
@[expose] noncomputable def thetaFun (G₁ : Subgroup G) (Φ : MulAut (↥G₁ ⧸ center ↥G₁) →* Q)
    (t n : G) : Wr Q :=
  if n ∈ normalizer (G₁ : Set G) then ⟨psiT G₁ Φ n, psiT G₁ Φ (t⁻¹ * n * t), false⟩
  else ⟨psiT G₁ Φ (n * t), psiT G₁ Φ (t * n), true⟩

theorem thetaFun_of_mem (G₁ : Subgroup G) (Φ : MulAut (↥G₁ ⧸ center ↥G₁) →* Q) (t : G) {n : G}
    (h : n ∈ normalizer (G₁ : Set G)) :
    thetaFun G₁ Φ t n = ⟨psiT G₁ Φ n, psiT G₁ Φ (t⁻¹ * n * t), false⟩ := by
  simp [thetaFun, h]

theorem thetaFun_of_not_mem (G₁ : Subgroup G) (Φ : MulAut (↥G₁ ⧸ center ↥G₁) →* Q) (t : G)
    {n : G} (h : n ∉ normalizer (G₁ : Set G)) :
    thetaFun G₁ Φ t n = ⟨psiT G₁ Φ (n * t), psiT G₁ Φ (t * n), true⟩ := by
  simp [thetaFun, h]

variable {G₁ G₂ : Subgroup G} {t : G} (Φ : MulAut (↥G₁ ⧸ center ↥G₁) →* Q)

theorem thetaFun_mul [Finite G] (c : CompData G₁ G₂ t) {n m : G}
    (hn : n ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G))
    (hm : m ∈ normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) :
    thetaFun G₁ Φ t (n * m) = thetaFun G₁ Φ t n * thetaFun G₁ Φ t m := by
  have hti : t⁻¹ = t := c.t_inv
  by_cases hn' : n ∈ normalizer (G₁ : Set G) <;> by_cases hm' : m ∈ normalizer (G₁ : Set G)
  ·
    have hnm : n * m ∈ normalizer (G₁ : Set G) := mul_mem hn' hm'
    rw [thetaFun_of_mem G₁ Φ t hnm, thetaFun_of_mem G₁ Φ t hn', thetaFun_of_mem G₁ Φ t hm',
      Wr.mk_mul_mk_false]
    refine Wr.ext ?_ ?_ rfl
    · exact psiT_mul G₁ Φ hn' hm'
    · have e : t⁻¹ * (n * m) * t = t⁻¹ * n * t * (t⁻¹ * m * t) := by group
      show psiT G₁ Φ (t⁻¹ * (n * m) * t) = _
      rw [e]
      exact psiT_mul G₁ Φ (c.conj_t_mem hn hn') (c.conj_t_mem hm hm')
  ·
    have hnm : n * m ∉ normalizer (G₁ : Set G) := fun h =>
      hm' (by simpa using mul_mem (inv_mem hn') h)
    rw [thetaFun_of_mem G₁ Φ t hn', thetaFun_of_not_mem G₁ Φ t hm',
      thetaFun_of_not_mem G₁ Φ t hnm, Wr.mk_mul_mk_false]
    refine Wr.ext ?_ ?_ rfl
    · have e : n * m * t = n * (m * t) := by group
      show psiT G₁ Φ (n * m * t) = _
      rw [e]
      exact psiT_mul G₁ Φ hn' (c.mul_t_mem hm hm')
    · have e : t * (n * m) = t⁻¹ * n * t * (t * m) := by
        rw [hti]
        calc t * (n * m) = t * n * (t * t) * m := by rw [c.t_sq]; group
          _ = t * n * t * (t * m) := by group
      show psiT G₁ Φ (t * (n * m)) = _
      rw [e]
      exact psiT_mul G₁ Φ (c.conj_t_mem hn hn') (c.t_mul_mem hm hm')
  ·
    have hnm : n * m ∉ normalizer (G₁ : Set G) := fun h =>
      hn' (by simpa using mul_mem h (inv_mem hm'))
    rw [thetaFun_of_not_mem G₁ Φ t hn', thetaFun_of_mem G₁ Φ t hm',
      thetaFun_of_not_mem G₁ Φ t hnm, Wr.mk_mul_mk_true]
    refine Wr.ext ?_ ?_ rfl
    · have e : n * m * t = n * t * (t⁻¹ * m * t) := by group
      show psiT G₁ Φ (n * m * t) = _
      rw [e]
      exact psiT_mul G₁ Φ (c.mul_t_mem hn hn') (c.conj_t_mem hm hm')
    · have e : t * (n * m) = t * n * m := by group
      show psiT G₁ Φ (t * (n * m)) = _
      rw [e]
      exact psiT_mul G₁ Φ (c.t_mul_mem hn hn') hm'
  ·
    have hnm : n * m ∈ normalizer (G₁ : Set G) := by
      rw [mem_normalizer_iff_cs, cs_mul, (c.swap_of_not_mem hm hm').1]
      exact (c.swap_of_not_mem hn hn').2
    rw [thetaFun_of_not_mem G₁ Φ t hn', thetaFun_of_not_mem G₁ Φ t hm',
      thetaFun_of_mem G₁ Φ t hnm, Wr.mk_mul_mk_true]
    refine Wr.ext ?_ ?_ rfl
    · have e : n * m = n * t * (t * m) := by
        calc n * m = n * (t * t) * m := by rw [c.t_sq]; group
          _ = n * t * (t * m) := by group
      show psiT G₁ Φ (n * m) = _
      rw [e]
      exact psiT_mul G₁ Φ (c.mul_t_mem hn hn') (c.t_mul_mem hm hm')
    · have e : t⁻¹ * (n * m) * t = t * n * (m * t) := by rw [hti]; group
      show psiT G₁ Φ (t⁻¹ * (n * m) * t) = _
      rw [e]
      exact psiT_mul G₁ Φ (c.t_mul_mem hn hn') (c.mul_t_mem hm hm')

@[expose] noncomputable def theta [Finite G] (c : CompData G₁ G₂ t) :
    ↥(normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G)) →* Wr Q where
  toFun n := thetaFun G₁ Φ t n
  map_one' := by
    show thetaFun G₁ Φ t 1 = 1
    rw [thetaFun_of_mem G₁ Φ t (one_mem _)]
    have : t⁻¹ * 1 * t = 1 := by group
    rw [this, psiT_one, Wr.one_def]
  map_mul' n m := thetaFun_mul Φ c n.2 m.2

theorem theta_apply [Finite G] (c : CompData G₁ G₂ t)
    (n : ↥(normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G))) :
    theta Φ c n = thetaFun G₁ Φ t n := rfl

theorem theta_e [Finite G] (c : CompData G₁ G₂ t)
    (n : ↥(normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G))) :
    (theta Φ c n).e = false ↔ (n : G) ∈ normalizer (G₁ : Set G) := by
  by_cases h : (n : G) ∈ normalizer (G₁ : Set G)
  · rw [theta_apply, thetaFun_of_mem G₁ Φ t h]
    simp [h]
  · rw [theta_apply, thetaFun_of_not_mem G₁ Φ t h]
    simp [h]

theorem theta_t [Finite G] (c : CompData G₁ G₂ t) :
    theta Φ c ⟨t, c.t_mem_normalizer⟩ = Wr.swap := by
  rw [theta_apply]
  show thetaFun G₁ Φ t t = _
  rw [thetaFun_of_not_mem G₁ Φ t c.t_not_mem, c.t_sq, psiT_one]
  rfl

theorem theta_eq_one [Finite G] (c : CompData G₁ G₂ t) (hΦ : Function.Injective Φ)
    (n : ↥(normalizer ((G₁ ⊔ G₂ : Subgroup G) : Set G))) (h : theta Φ c n = 1) :
    (n : G) ∈ centralizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) := by
  have hn' : (n : G) ∈ normalizer (G₁ : Set G) := by
    rw [← theta_e Φ c n, h]
    rfl
  rw [theta_apply, thetaFun_of_mem G₁ Φ t hn'] at h
  have h1 : psiT G₁ Φ n = 1 := congrArg Wr.a h
  have h2 : psiT G₁ Φ (t⁻¹ * n * t) = 1 := congrArg Wr.b h
  have hcn : ∀ x ∈ G₁, (n : G) * x = x * n := by
    intro x hx
    rw [psiT_of_mem G₁ Φ hn'] at h1
    have : actQ G₁ ⟨n, hn'⟩ = 1 := hΦ (h1.trans (map_one Φ).symm)
    exact centralizes_of_actQ_eq_one c.perfect this hx
  have hn2 : t⁻¹ * n * t ∈ normalizer (G₁ : Set G) := c.conj_t_mem n.2 hn'
  have hct : ∀ x ∈ G₁, t⁻¹ * n * t * x = x * (t⁻¹ * n * t) := by
    intro x hx
    rw [psiT_of_mem G₁ Φ hn2] at h2
    have : actQ G₁ ⟨t⁻¹ * n * t, hn2⟩ = 1 := hΦ (h2.trans (map_one Φ).symm)
    exact centralizes_of_actQ_eq_one c.perfect this hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyc : G₁ ⊔ G₂ ≤ centralizer ({(n : G)} : Set G) := by
    refine sup_le ?_ ?_
    · intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcn z hz).symm
    · intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hz' : t⁻¹ * z * t ∈ G₁ := (c.swap z).1 hz
      have := hct _ hz'
      have e1 : t⁻¹ * (n : G) * t * (t⁻¹ * z * t) = t⁻¹ * ((n : G) * z) * t := by group
      have e2 : t⁻¹ * z * t * (t⁻¹ * (n : G) * t) = t⁻¹ * (z * (n : G)) * t := by group
      rw [e1, e2] at this
      exact (mul_left_cancel (mul_right_cancel this)).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hyc hy)).symm.symm

end Theta

end CFSG.OddStandard.Seitz77.CaseB45
