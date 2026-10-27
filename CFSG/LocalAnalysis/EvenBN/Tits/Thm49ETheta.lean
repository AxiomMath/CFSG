module

public import CFSG.LocalAnalysis.EvenBN.Tits.Thm49ECtx

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Thm49E

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits.Model

section Aux

variable {G : Type} [Group G]

private theorem memC_iff {t x : G} : x ∈ centralizer ({t} : Set G) ↔ x * t = t * x :=
  Subgroup.mem_centralizer_singleton_iff

private theorem conj_comm (v : G) {a b : G} (h : a * b = b * a) :
    v * a * v⁻¹ * (v * b * v⁻¹) = v * b * v⁻¹ * (v * a * v⁻¹) := by
  calc v * a * v⁻¹ * (v * b * v⁻¹) = v * (a * b) * v⁻¹ := by group
    _ = v * (b * a) * v⁻¹ := by rw [h]
    _ = v * b * v⁻¹ * (v * a * v⁻¹) := by group

private theorem comm_z_of {t z x : G} (htt : t * t = 1) (hxt : x * t = t * x)
    (hxQ : x * (t * z) = (t * z) * x) : x * z = z * x := by
  have h : x * (t * (t * z)) = (t * (t * z)) * x := Commute.mul_right hxt hxQ
  rwa [← mul_assoc t t z, htt, one_mul] at h

private theorem comm_Q_of {t z x : G} (hxt : x * t = t * x) (hxz : x * z = z * x) :
    x * (t * z) = (t * z) * x := Commute.mul_right hxt hxz

private structure Tri3 (P Q R x : G) : Prop where
  hP : x * P = P * x
  hQ : x * Q = Q * x
  hR : x * R = R * x

private theorem Tri3.conj {P Q R u w : G} (h : Tri3 P Q R u) (eQ : w * Q * w⁻¹ = P)
    (eR : w * R * w⁻¹ = Q) (eP : w * P * w⁻¹ = R) : Tri3 P Q R (w * u * w⁻¹) where
  hP := by have := conj_comm w h.hQ; rwa [eQ] at this
  hQ := by have := conj_comm w h.hR; rwa [eR] at this
  hR := by have := conj_comm w h.hP; rwa [eP] at this

private theorem Tri3.of_conj {P Q R W : G} (hP : W * P * W⁻¹ = P) (hQ : W * Q * W⁻¹ = Q)
    (hR : W * R * W⁻¹ = R) : Tri3 P Q R W where
  hP := mul_inv_eq_iff_eq_mul.1 hP
  hQ := mul_inv_eq_iff_eq_mul.1 hQ
  hR := mul_inv_eq_iff_eq_mul.1 hR

private theorem inA_mul (a b : Equiv.Perm (Fin 1755)) : inA a * inA b = inA (a * b) := by
  simp [inA]

private theorem inA_inv (a : Equiv.Perm (Fin 1755)) : (inA a)⁻¹ = inA a⁻¹ := by
  simp [inA]

private theorem mem_GammaH_iff {a : Cm} :
    a ∈ GammaH ↔ a ∈ Am ∧ a * inA titsZ = inA titsZ * a := by
  unfold GammaH
  rw [Subgroup.mem_inf, memC_iff]

private theorem mem_KH_iff {zp : Equiv.Perm (Fin 1755)} {a : Cm} :
    a ∈ KH zp ↔ (a ∈ Am ∧ a * inA titsZ = inA titsZ * a) ∧
      a * (tauH * inA zp) = (tauH * inA zp) * a := by
  unfold KH
  rw [Subgroup.mem_inf, memC_iff, mem_GammaH_iff]

private theorem mem_MH_iff {m : Cm} :
    m ∈ MH ↔ m = tauH ∨ ∃ l, IsLong l ∧ l * titsZ = titsZ * l ∧ m = tauH * inA l := Iff.rfl

open Classical in
private noncomputable def phiX (c : Ctx G) (g : G) : Cm :=
  if h : g ∈ centralizer ({c.t} : Set G) then c.Φ ⟨g, h⟩ else 1

private noncomputable def psiX (c : Ctx G) (a : Cm) : G :=
  ((Function.invFun c.Φ a : ↥(centralizer ({c.t} : Set G))) : G)

variable (c : Ctx G)

private theorem phiX_eq {g : G} (h : g ∈ centralizer ({c.t} : Set G)) :
    phiX c g = c.Φ ⟨g, h⟩ := dif_pos h

private theorem phiX_mul {x y : G} (hx : x ∈ centralizer ({c.t} : Set G))
    (hy : y ∈ centralizer ({c.t} : Set G)) : phiX c (x * y) = phiX c x * phiX c y := by
  rw [phiX_eq c hx, phiX_eq c hy, phiX_eq c (mul_mem hx hy)]
  exact c.Φ.map_mul ⟨x, hx⟩ ⟨y, hy⟩

private theorem phiX_inv {x : G} (hx : x ∈ centralizer ({c.t} : Set G)) :
    phiX c x⁻¹ = (phiX c x)⁻¹ := by
  rw [phiX_eq c hx, phiX_eq c (inv_mem hx)]
  exact c.Φ.map_inv ⟨x, hx⟩

private theorem phiX_inj {x y : G} (hx : x ∈ centralizer ({c.t} : Set G))
    (hy : y ∈ centralizer ({c.t} : Set G)) (h : phiX c x = phiX c y) : x = y := by
  rw [phiX_eq c hx, phiX_eq c hy] at h
  exact congrArg Subtype.val (c.inj h)

private theorem phiX_mem {x : G} (hx : x ∈ centralizer ({c.t} : Set G)) : phiX c x ∈ Am := by
  rw [phiX_eq c hx]
  exact c.mem_Am _

private theorem psiX_mem {a : Cm} (_ : a ∈ Am) : psiX c a ∈ centralizer ({c.t} : Set G) :=
  (Function.invFun c.Φ a).2

private theorem phiX_psiX {a : Cm} (ha : a ∈ Am) : phiX c (psiX c a) = a := by
  obtain ⟨x, hx⟩ := c.surj a ha
  rw [phiX_eq c (psiX_mem c ha)]
  exact Function.invFun_eq (f := c.Φ) ⟨x, hx⟩

private theorem psiX_phiX {x : G} (hx : x ∈ centralizer ({c.t} : Set G)) :
    psiX c (phiX c x) = x :=
  phiX_inj c (psiX_mem c (phiX_mem c hx)) hx (phiX_psiX c (phiX_mem c hx))

private theorem comm_of_phiX {x y : G} (hx : x ∈ centralizer ({c.t} : Set G))
    (hy : y ∈ centralizer ({c.t} : Set G)) (h : phiX c x * phiX c y = phiX c y * phiX c x) :
    x * y = y * x :=
  phiX_inj c (mul_mem hx hy) (mul_mem hy hx) (by rw [phiX_mul c hx hy, phiX_mul c hy hx]; exact h)

private theorem phiX_comm {x y : G} (hx : x ∈ centralizer ({c.t} : Set G))
    (hy : y ∈ centralizer ({c.t} : Set G)) (h : x * y = y * x) :
    phiX c x * phiX c y = phiX c y * phiX c x := by
  rw [← phiX_mul c hx hy, ← phiX_mul c hy hx, h]

end Aux

theorem Ctx.false_of_swap {G : Type} [Group G] (c : Ctx G) {zp y0 : Equiv.Perm (Fin 1755)}
    (hF6 : F6Facts zp y0) (hTO : TOHat zp y0)
    {z z' y₁ v : G} (hz : z ∈ centralizer ({c.t} : Set G))
    (hz' : z' ∈ centralizer ({c.t} : Set G)) (hy : y₁ ∈ centralizer ({c.t} : Set G))
    (hΦz : c.Φ ⟨z, hz⟩ = inA titsZ) (hΦz' : c.Φ ⟨z', hz'⟩ = inA zp)
    (hΦy : c.Φ ⟨y₁, hy⟩ = inA y0)
    (hvP : v * c.t * v⁻¹ = c.t * z) (hvQ : v * (c.t * z) * v⁻¹ = c.t)
    (hvR : v * (c.t * z') * v⁻¹ = c.t * z') : False := by
  have htt : c.t * c.t = 1 := c.t_sq
  have htC : c.t ∈ centralizer ({c.t} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hzt : z * c.t = c.t * z := memC_iff.1 hz
  have hyt : y₁ * c.t = c.t * y₁ := memC_iff.1 hy
  have hRC : c.t * z' ∈ centralizer ({c.t} : Set G) := mul_mem htC hz'
  have hΦ'z : phiX c z = inA titsZ := (phiX_eq c hz).trans hΦz
  have hΦ'z' : phiX c z' = inA zp := (phiX_eq c hz').trans hΦz'
  have hΦ'y : phiX c y₁ = inA y0 := (phiX_eq c hy).trans hΦy
  have hΦ't : phiX c c.t = tauH := (phiX_eq c htC).trans c.map_t
  have hΦ'Q : phiX c (c.t * z) = tauH * inA titsZ := by
    rw [phiX_mul c htC hz, hΦ't, hΦ'z]
  have hΦ'R : phiX c (c.t * z') = tauH * inA zp := by
    rw [phiX_mul c htC hz', hΦ't, hΦ'z']
  have hvz : v * z * v⁻¹ = z := by
    have h1 : v * (c.t * (c.t * z)) * v⁻¹ = v * c.t * v⁻¹ * (v * (c.t * z) * v⁻¹) := by group
    rw [← mul_assoc c.t c.t z, htt, one_mul, hvP, hvQ] at h1
    rw [h1, mul_assoc, hzt, ← mul_assoc, htt, one_mul]
  have hyz : y₁ * z * y₁⁻¹ = z' := by
    refine phiX_inj c (mul_mem (mul_mem hy hz) (inv_mem hy)) hz' ?_
    rw [phiX_mul c (mul_mem hy hz) (inv_mem hy), phiX_mul c hy hz, phiX_inv c hy, hΦ'y, hΦ'z,
      hΦ'z', inA_inv, inA_mul, inA_mul, hF6.y0_z]
  have hyz' : y₁ * z' * y₁⁻¹ = z := by
    refine phiX_inj c (mul_mem (mul_mem hy hz') (inv_mem hy)) hz ?_
    rw [phiX_mul c (mul_mem hy hz') (inv_mem hy), phiX_mul c hy hz', phiX_inv c hy, hΦ'y, hΦ'z',
      hΦ'z, inA_inv, inA_mul, inA_mul, hF6.y0_zp]
  have hyP : y₁ * c.t * y₁⁻¹ = c.t := by rw [hyt]; group
  obtain ⟨w, hw⟩ : ∃ w : G, w = y₁ * v := ⟨_, rfl⟩
  have hwc : ∀ a : G, w * a * w⁻¹ = y₁ * (v * a * v⁻¹) * y₁⁻¹ := by
    intro a
    rw [hw]
    group
  have hwP : w * c.t * w⁻¹ = c.t * z' := by
    rw [hwc, hvP]
    calc y₁ * (c.t * z) * y₁⁻¹ = (y₁ * c.t * y₁⁻¹) * (y₁ * z * y₁⁻¹) := by group
      _ = c.t * z' := by rw [hyP, hyz]
  have hwQ : w * (c.t * z) * w⁻¹ = c.t := by rw [hwc, hvQ, hyP]
  have hwR : w * (c.t * z') * w⁻¹ = c.t * z := by
    rw [hwc, hvR]
    calc y₁ * (c.t * z') * y₁⁻¹ = (y₁ * c.t * y₁⁻¹) * (y₁ * z' * y₁⁻¹) := by group
      _ = c.t * z := by rw [hyP, hyz']
  have hKW : Tri3 c.t (c.t * z) (c.t * z') (w * w * w) := by
    refine Tri3.of_conj ?_ ?_ ?_
    · calc w * w * w * c.t * (w * w * w)⁻¹ = w * (w * (w * c.t * w⁻¹) * w⁻¹) * w⁻¹ := by group
        _ = c.t := by rw [hwP, hwR, hwQ]
    · calc w * w * w * (c.t * z) * (w * w * w)⁻¹
          = w * (w * (w * (c.t * z) * w⁻¹) * w⁻¹) * w⁻¹ := by group
        _ = c.t * z := by rw [hwQ, hwP, hwR]
    · calc w * w * w * (c.t * z') * (w * w * w)⁻¹
          = w * (w * (w * (c.t * z') * w⁻¹) * w⁻¹) * w⁻¹ := by group
        _ = c.t * z' := by rw [hwR, hwQ, hwP]
  have hKconj : ∀ u, Tri3 c.t (c.t * z) (c.t * z') u →
      Tri3 c.t (c.t * z) (c.t * z') (w * u * w⁻¹) := fun u hu => hu.conj hwQ hwR hwP
  obtain ⟨s, hs⟩ : ∃ s : Cm → Cm, ∀ a, s a = phiX c (v * psiX c a * v⁻¹) := ⟨_, fun a => rfl⟩
  have hLzv : ∀ x : G, x * c.t = c.t * x → x * z = z * x →
      v * x * v⁻¹ * c.t = c.t * (v * x * v⁻¹) ∧ v * x * v⁻¹ * z = z * (v * x * v⁻¹) := by
    intro x hxt hxz
    constructor
    · have := conj_comm v (comm_Q_of hxt hxz)
      rwa [hvQ] at this
    · have := conj_comm v hxz
      rwa [hvz] at this
  have hxa : ∀ a ∈ GammaH, psiX c a ∈ centralizer ({c.t} : Set G) ∧ phiX c (psiX c a) = a ∧
      psiX c a * z = z * psiX c a := by
    intro a ha
    obtain ⟨haA, haz⟩ := mem_GammaH_iff.1 ha
    have hxC := psiX_mem c haA
    have hxa := phiX_psiX c haA
    exact ⟨hxC, hxa, comm_of_phiX c hxC hz (by rw [hxa, hΦ'z]; exact haz)⟩
  have hvx : ∀ a ∈ GammaH, v * psiX c a * v⁻¹ ∈ centralizer ({c.t} : Set G) ∧
      v * psiX c a * v⁻¹ * z = z * (v * psiX c a * v⁻¹) := by
    intro a ha
    obtain ⟨hxC, -, hxz⟩ := hxa a ha
    obtain ⟨h1, h2⟩ := hLzv _ (memC_iff.1 hxC) hxz
    exact ⟨memC_iff.2 h1, h2⟩
  have hs_mem : ∀ a ∈ GammaH, s a ∈ GammaH := by
    intro a ha
    obtain ⟨hyC, hyz⟩ := hvx a ha
    rw [hs]
    refine mem_GammaH_iff.2 ⟨phiX_mem c hyC, ?_⟩
    have := phiX_comm c hyC hz hyz
    rwa [hΦ'z] at this
  have hs_mul : ∀ a ∈ GammaH, ∀ b ∈ GammaH, s (a * b) = s a * s b := by
    intro a ha b hb
    obtain ⟨hxC, hxa', -⟩ := hxa a ha
    obtain ⟨hyC, hyb', -⟩ := hxa b hb
    obtain ⟨hvxC, -⟩ := hvx a ha
    obtain ⟨hvyC, -⟩ := hvx b hb
    have hab : psiX c (a * b) = psiX c a * psiX c b := by
      have h : a * b = phiX c (psiX c a * psiX c b) := by
        rw [phiX_mul c hxC hyC, hxa', hyb']
      rw [h, psiX_phiX c (mul_mem hxC hyC)]
    have h2 : v * (psiX c a * psiX c b) * v⁻¹ = (v * psiX c a * v⁻¹) * (v * psiX c b * v⁻¹) := by
      group
    simp only [hs, hab]
    rw [h2, phiX_mul c hvxC hvyC]
  have hs_inj : ∀ a ∈ GammaH, ∀ b ∈ GammaH, s a = s b → a = b := by
    intro a ha b hb hab
    obtain ⟨hxC, hxa', -⟩ := hxa a ha
    obtain ⟨hyC, hyb', -⟩ := hxa b hb
    obtain ⟨hvxC, -⟩ := hvx a ha
    obtain ⟨hvyC, -⟩ := hvx b hb
    simp only [hs] at hab
    have h1 := phiX_inj c hvxC hvyC hab
    have h2 : psiX c a = psiX c b := mul_left_cancel (mul_right_cancel h1)
    calc a = phiX c (psiX c a) := hxa'.symm
      _ = phiX c (psiX c b) := by rw [h2]
      _ = b := hyb'
  have hpsi_t : psiX c tauH = c.t := by
    have := psiX_phiX c htC
    rwa [hΦ't] at this
  have hpsi_z : psiX c (inA titsZ) = z := by
    have := psiX_phiX c hz
    rwa [hΦ'z] at this
  have hpsi_R : psiX c (tauH * inA zp) = c.t * z' := by
    have := psiX_phiX c hRC
    rwa [hΦ'R] at this
  have hs_tau : s tauH = tauH * inA titsZ := by rw [hs, hpsi_t, hvP, hΦ'Q]
  have hs_z : s (inA titsZ) = inA titsZ := by rw [hs, hpsi_z, hvz, hΦ'z]
  have hs_R : s (tauH * inA zp) = tauH * inA zp := by rw [hs, hpsi_R, hvR, hΦ'R]
  have hs_MH : ∀ m ∈ MH, m ∈ GammaH → s m ∈ MH := by
    intro m hm hmG
    obtain ⟨hxC, hxm, hxz⟩ := hxa m hmG
    obtain ⟨hvC, -⟩ := hvx m hmG
    have hΦx : c.Φ ⟨psiX c m, hxC⟩ = m := (phiX_eq c hxC).symm.trans hxm
    obtain ⟨g, hg⟩ : ∃ g : G, g * c.t * g⁻¹ = psiX c m := by
      refine (c.I2 ⟨psiX c m, hxC⟩).2 ?_
      rw [hΦx]
      rcases mem_MH_iff.1 hm with h | ⟨l, hl, -, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨l, hl, h⟩
    have hI := (c.I2 ⟨v * psiX c m * v⁻¹, hvC⟩).1
      ⟨v * g, by
        show v * g * c.t * (v * g)⁻¹ = v * psiX c m * v⁻¹
        rw [← hg]
        group⟩
    have hsm : s m = c.Φ ⟨v * psiX c m * v⁻¹, hvC⟩ := by
      rw [hs]
      exact phiX_eq c hvC
    have hsG := hs_mem m hmG
    rw [hsm] at hsG ⊢
    rcases hI with h | ⟨l', hl', h⟩
    · exact mem_MH_iff.2 (Or.inl h)
    · refine mem_MH_iff.2 (Or.inr ⟨l', hl', ?_, h⟩)
      rw [h] at hsG
      have hcomm := congrArg Prod.snd (mem_GammaH_iff.1 hsG).2
      simpa [tauH, inA] using hcomm
  obtain ⟨θ, hθ⟩ : ∃ θ : Cm → Cm, ∀ x, θ x = inA y0 * s x * (inA y0)⁻¹ := ⟨_, fun x => rfl⟩
  have hΘ1 : ∀ u, Tri3 c.t (c.t * z) (c.t * z') u → θ (phiX c u) = phiX c (w * u * w⁻¹) := by
    intro u hu
    have huC : u ∈ centralizer ({c.t} : Set G) := memC_iff.2 hu.hP
    obtain ⟨h1, -⟩ := hLzv u hu.hP (comm_z_of htt hu.hP hu.hQ)
    have hvC : v * u * v⁻¹ ∈ centralizer ({c.t} : Set G) := memC_iff.2 h1
    calc θ (phiX c u) = inA y0 * phiX c (v * u * v⁻¹) * (inA y0)⁻¹ := by
          rw [hθ, hs, psiX_phiX c huC]
      _ = phiX c (y₁ * (v * u * v⁻¹) * y₁⁻¹) := by
          rw [phiX_mul c (mul_mem hy hvC) (inv_mem hy), phiX_mul c hy hvC, phiX_inv c hy, hΦ'y]
      _ = phiX c (w * u * w⁻¹) := by rw [hwc]
  have hWC : w * w * w ∈ centralizer ({c.t} : Set G) := memC_iff.2 hKW.hP
  have hdKH : phiX c (w * w * w) ∈ KH zp := by
    refine mem_KH_iff.2 ⟨⟨phiX_mem c hWC, ?_⟩, ?_⟩
    · have := phiX_comm c hWC hz (comm_z_of htt hKW.hP hKW.hQ)
      rwa [hΦ'z] at this
    · have := phiX_comm c hWC hRC hKW.hR
      rwa [hΦ'R] at this
  have hKH : ∀ g ∈ KH zp, ∃ u, Tri3 c.t (c.t * z) (c.t * z') u ∧ phiX c u = g := by
    intro g hg
    obtain ⟨⟨hgA, hgz⟩, hgR⟩ := mem_KH_iff.1 hg
    have huC := psiX_mem c hgA
    have hug := phiX_psiX c hgA
    have huz : psiX c g * z = z * psiX c g :=
      comm_of_phiX c huC hz (by rw [hug, hΦ'z]; exact hgz)
    have hut : psiX c g * c.t = c.t * psiX c g := memC_iff.1 huC
    exact ⟨psiX c g, ⟨hut, comm_Q_of hut huz,
      comm_of_phiX c huC hRC (by rw [hug, hΦ'R]; exact hgR)⟩, hug⟩
  refine hTO s hs_mul hs_mem hs_inj hs_tau hs_z hs_R hs_MH θ hθ ⟨phiX c (w * w * w), hdKH, ?_⟩
  intro g hg
  obtain ⟨u, hu, rfl⟩ := hKH g hg
  have huC : u ∈ centralizer ({c.t} : Set G) := memC_iff.2 hu.hP
  have h3 : w * (w * (w * u * w⁻¹) * w⁻¹) * w⁻¹ = (w * w * w) * u * (w * w * w)⁻¹ := by group
  rw [hΘ1 u hu, hΘ1 _ (hKconj u hu), hΘ1 _ (hKconj _ (hKconj u hu)), h3,
    phiX_mul c (mul_mem hWC huC) (inv_mem hWC), phiX_mul c hWC huC, phiX_inv c hWC]

end CFSG.LocalAnalysis.EvenBN.Tits.Thm49E
