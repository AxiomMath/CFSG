module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.NormalizerD
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SL7V8Facts
public import CFSG.LargeExtraspecial.S45QLin
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

theorem ThCyc.normalizer_D_le_normalizer_omega1 {G : Type} [Group G] {A Aa D : Subgroup G} {t : G}
    (hD : DHyp A Aa t D) : normalizer (D : Set G) ≤ normalizer (omega1 D hD.comm : Set G) := by
  intro g hg
  refine mem_normalizer_iff.2 fun v => ⟨?_, ?_⟩
  · rintro ⟨hvD, hv2⟩
    refine mem_omega1_iff.2 ⟨(mem_normalizer_iff.1 hg v).1 hvD, ?_⟩
    calc (g * v * g⁻¹) ^ 2 = g * v ^ 2 * g⁻¹ := by rw [sq, sq]; group
      _ = 1 := by rw [hv2]; group
  · intro hv
    have hg' : g⁻¹ ∈ normalizer (D : Set G) := (normalizer (D : Set G)).inv_mem hg
    have hvD : g⁻¹ * (g * v * g⁻¹) * g ∈ D := by
      have h := (mem_normalizer_iff.1 hg' (g * v * g⁻¹)).1 (mem_omega1_iff.1 hv).1
      simpa using h
    have hv2 : (g⁻¹ * (g * v * g⁻¹) * g) ^ 2 = 1 := by
      calc (g⁻¹ * (g * v * g⁻¹) * g) ^ 2 = g⁻¹ * (g * v * g⁻¹) ^ 2 * g := by
            rw [sq, sq]; group
        _ = 1 := by rw [(mem_omega1_iff.1 hv).2]; group
    have e : g⁻¹ * (g * v * g⁻¹) * g = v := by group
    rw [e] at hvD hv2
    exact mem_omega1_iff.2 ⟨hvD, hv2⟩

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

theorem ThCyc.normalizer_D_le_normalizer_A (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) :
    normalizer (D : Set G) ≤ normalizer (A : Set G) := by
  intro g hg
  refine mem_normalizer_iff.2 fun a => ⟨?_, ?_⟩
  · intro ha
    obtain ⟨x, hx, rfl⟩ := (W2.A_eq_sq a).1 ha
    have hgx : g * x * g⁻¹ ∈ D := (mem_normalizer_iff.1 hg x).1 (hD.Aa_le hx)
    have hsq := H.D_sq_mem_A_of_fourth W W2 hD h4 hgx
    have e : g * x ^ 2 * g⁻¹ = (g * x * g⁻¹) ^ 2 := by rw [sq, sq]; group
    rw [e]
    exact hsq
  · intro ha
    obtain ⟨x, hx, hx2⟩ := (W2.A_eq_sq (g * a * g⁻¹)).1 ha
    have hg' : g⁻¹ ∈ normalizer (D : Set G) := (normalizer (D : Set G)).inv_mem hg
    have hgx : g⁻¹ * x * g ∈ D := by
      have h := (mem_normalizer_iff.1 hg' x).1 (hD.Aa_le hx)
      simpa using h
    have hsq := H.D_sq_mem_A_of_fourth W W2 hD h4 hgx
    have e : a = (g⁻¹ * x * g) ^ 2 := by
      calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = g⁻¹ * x ^ 2 * g := by rw [hx2]
        _ = (g⁻¹ * x * g) ^ 2 := by rw [sq, sq]; group
    rw [e]
    exact hsq

private def hsqOf (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) : ∀ d ∈ D, d ^ 2 ∈ A :=
  fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd

private noncomputable def psiPre (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) (a : ↥A) : G :=
  Classical.choose (H.thV_surj W W2 hD (hsqOf H W W2 hD h4) a a.2)

private theorem psiPre_mem (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) (a : ↥A) :
    psiPre H W W2 hD h4 a ∈ omega1 D hD.comm :=
  (Classical.choose_spec (H.thV_surj W W2 hD (hsqOf H W W2 hD h4) a a.2)).1

private theorem psiPre_val (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) (a : ↥A) :
    thV t (psiPre H W W2 hD h4 a) = (a : G) :=
  (Classical.choose_spec (H.thV_surj W W2 hD (hsqOf H W W2 hD h4) a a.2)).2

private theorem thV_inv (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) {v : G} (hv : v ∈ omega1 D hD.comm) : thV t v⁻¹ = (thV t v)⁻¹ := by
  have hv' : v⁻¹ ∈ omega1 D hD.comm := (omega1 D hD.comm).inv_mem hv
  have h := H.thV_mul W W2 hD hv' hv
  have h1 : thV t (v⁻¹ * v) = 1 := by simp [thV]
  rw [h1] at h
  have h2 : thV t v⁻¹ * thV t v * (thV t v)⁻¹ = (thV t v)⁻¹ := by rw [h.symm, one_mul]
  rwa [mul_assoc, mul_inv_cancel, mul_one] at h2

private theorem phiFun_wd (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {g : G} (hg : g ∈ normalizer (D : Set G))
    {v w : G} (hv : v ∈ omega1 D hD.comm) (hw : w ∈ omega1 D hD.comm) (hvw : thV t v = thV t w) :
    thV t (g * v * g⁻¹) = thV t (g * w * g⁻¹) := by
  have hgV := ThCyc.normalizer_D_le_normalizer_omega1 hD hg
  have hgA := H.normalizer_D_le_normalizer_A W W2 hD h4 hg
  have hgv : g * v * g⁻¹ ∈ omega1 D hD.comm := (mem_normalizer_iff.1 hgV v).1 hv
  have hvwV : v⁻¹ * w ∈ omega1 D hD.comm :=
    (omega1 D hD.comm).mul_mem ((omega1 D hD.comm).inv_mem hv) hw
  have hψ : thV t (v⁻¹ * w) = 1 := by
    rw [H.thV_mul W W2 hD ((omega1 D hD.comm).inv_mem hv) hw,
      thV_inv H W W2 hD hv, hvw, inv_mul_cancel]
  have hA : v⁻¹ * w ∈ A := (H.thV_eq_one_iff W W2 hD hvwV).1 hψ
  have hgA' : g * (v⁻¹ * w) * g⁻¹ ∈ A := (mem_normalizer_iff.1 hgA (v⁻¹ * w)).1 hA
  have hgA'' : g * (v⁻¹ * w) * g⁻¹ ∈ omega1 D hD.comm :=
    (mem_normalizer_iff.1 hgV (v⁻¹ * w)).1 hvwV
  have hψ2 : thV t (g * (v⁻¹ * w) * g⁻¹) = 1 :=
    (H.thV_eq_one_iff W W2 hD hgA'').2 hgA'
  have e : g * w * g⁻¹ = (g * v * g⁻¹) * (g * (v⁻¹ * w) * g⁻¹) := by group
  rw [e, H.thV_mul W W2 hD hgv hgA'', hψ2, mul_one]

private noncomputable def phiFun (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) (g : G)
    (hg : g ∈ normalizer (D : Set G)) (a : ↥A) : ↥A :=
  ⟨thV t (g * psiPre H W W2 hD h4 a * g⁻¹),
    H.thV_mem_A W W2 hD
      ((mem_normalizer_iff.1 (ThCyc.normalizer_D_le_normalizer_omega1 hD hg)
        (psiPre H W W2 hD h4 a)).1 (psiPre_mem H W W2 hD h4 a))⟩

private theorem phiFun_coe (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) (g : G) (hg : g ∈ normalizer (D : Set G))
    (a : ↥A) : ((phiFun H W W2 hD h4 g hg a : ↥A) : G) =
      thV t (g * psiPre H W W2 hD h4 a * g⁻¹) := rfl

private theorem phiFun_spec (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {g : G} (hg : g ∈ normalizer (D : Set G)) {v : G}
    (hv : v ∈ omega1 D hD.comm) : phiFun H W W2 hD h4 g hg ⟨thV t v, H.thV_mem_A W W2 hD hv⟩ =
      ⟨thV t (g * v * g⁻¹),
        H.thV_mem_A W W2 hD ((mem_normalizer_iff.1
          (ThCyc.normalizer_D_le_normalizer_omega1 hD hg) v).1 hv)⟩ := by
  apply Subtype.ext
  exact phiFun_wd H W W2 hD h4 hg (psiPre_mem H W W2 hD h4 _) hv (psiPre_val H W W2 hD h4 _)

private theorem phiFun_one (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) (a : ↥A) :
    phiFun H W W2 hD h4 1 (one_mem (normalizer (D : Set G))) a = a := by
  have ha : (⟨thV t (psiPre H W W2 hD h4 a),
      H.thV_mem_A W W2 hD (psiPre_mem H W W2 hD h4 a)⟩ : ↥A) = a :=
    Subtype.ext (psiPre_val H W W2 hD h4 a)
  rw [← ha, phiFun_spec H W W2 hD h4 (one_mem _) (psiPre_mem H W W2 hD h4 a)]
  apply Subtype.ext
  simpa using psiPre_val H W W2 hD h4 a

private theorem phiFun_mul (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {g h : G} (hg : g ∈ normalizer (D : Set G))
    (hh : h ∈ normalizer (D : Set G)) (a : ↥A) :
    phiFun H W W2 hD h4 (g * h) (Subgroup.mul_mem _ hg hh) a =
      phiFun H W W2 hD h4 g hg (phiFun H W W2 hD h4 h hh a) := by
  have hv := psiPre_mem H W W2 hD h4 a
  have hhV := ThCyc.normalizer_D_le_normalizer_omega1 hD hh
  have hhv : h * psiPre H W W2 hD h4 a * h⁻¹ ∈ omega1 D hD.comm :=
    (mem_normalizer_iff.1 hhV _).1 hv
  have h1 : thV t (psiPre H W W2 hD h4 (phiFun H W W2 hD h4 h hh a)) =
      thV t (h * psiPre H W W2 hD h4 a * h⁻¹) := by
    rw [psiPre_val H W W2 hD h4 (phiFun H W W2 hD h4 h hh a),
      phiFun_coe H W W2 hD h4 h hh a]
  have e1 : thV t ((g * h) * psiPre H W W2 hD h4 a * (g * h)⁻¹) =
      thV t (g * (h * psiPre H W W2 hD h4 a * h⁻¹) * g⁻¹) := by
    congr 1
    group
  have e2 := phiFun_wd H W W2 hD h4 hg hhv
    (psiPre_mem H W W2 hD h4 (phiFun H W W2 hD h4 h hh a)) h1.symm
  apply Subtype.ext
  rw [phiFun_coe, phiFun_coe, e1, e2]

private theorem phiFun_mul_apply (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) (g : G)
    (hg : g ∈ normalizer (D : Set G)) (a b : ↥A) : phiFun H W W2 hD h4 g hg (a * b) =
      phiFun H W W2 hD h4 g hg a * phiFun H W W2 hD h4 g hg b := by
  have hv := psiPre_mem H W W2 hD h4 a
  have hw := psiPre_mem H W W2 hD h4 b
  have hvwV : psiPre H W W2 hD h4 a * psiPre H W W2 hD h4 b ∈ omega1 D hD.comm :=
    (omega1 D hD.comm).mul_mem hv hw
  have h1 : thV t (psiPre H W W2 hD h4 (a * b)) =
      thV t (psiPre H W W2 hD h4 a * psiPre H W W2 hD h4 b) := by
    rw [psiPre_val H W W2 hD h4 (a * b), H.thV_mul W W2 hD hv hw,
      psiPre_val H W W2 hD h4 a, psiPre_val H W W2 hD h4 b]
    rfl
  have e1 := phiFun_wd H W W2 hD h4 hg (psiPre_mem H W W2 hD h4 (a * b)) hvwV h1
  have hgV := ThCyc.normalizer_D_le_normalizer_omega1 hD hg
  have hgv : g * psiPre H W W2 hD h4 a * g⁻¹ ∈ omega1 D hD.comm :=
    (mem_normalizer_iff.1 hgV _).1 hv
  have hgw : g * psiPre H W W2 hD h4 b * g⁻¹ ∈ omega1 D hD.comm :=
    (mem_normalizer_iff.1 hgV _).1 hw
  have e2 : g * (psiPre H W W2 hD h4 a * psiPre H W W2 hD h4 b) * g⁻¹ =
      (g * psiPre H W W2 hD h4 a * g⁻¹) * (g * psiPre H W W2 hD h4 b * g⁻¹) := by
    group
  apply Subtype.ext
  rw [phiFun_coe]
  simp only [Subgroup.coe_mul]
  rw [e1, e2, H.thV_mul W W2 hD hgv hgw]
  rw [phiFun_coe, phiFun_coe]

private noncomputable def phiAut (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) (g : G)
    (hg : g ∈ normalizer (D : Set G)) : MulAut ↥A where
  toFun := phiFun H W W2 hD h4 g hg
  invFun := phiFun H W W2 hD h4 g⁻¹ ((normalizer (D : Set G)).inv_mem hg)
  left_inv a := by
    have hv := psiPre_mem H W W2 hD h4 a
    have ha : (⟨thV t (psiPre H W W2 hD h4 a),
        H.thV_mem_A W W2 hD hv⟩ : ↥A) = a :=
      Subtype.ext (psiPre_val H W W2 hD h4 a)
    rw [← ha, phiFun_spec H W W2 hD h4 hg hv]
    rw [phiFun_spec H W W2 hD h4 ((normalizer (D : Set G)).inv_mem hg)
      (v := g * psiPre H W W2 hD h4 a * g⁻¹)
      ((mem_normalizer_iff.1 (ThCyc.normalizer_D_le_normalizer_omega1 hD hg) _).1 hv)]
    apply Subtype.ext
    simp only
    congr 1
    group
  right_inv a := by
    have hv := psiPre_mem H W W2 hD h4 a
    have ha : (⟨thV t (psiPre H W W2 hD h4 a),
        H.thV_mem_A W W2 hD hv⟩ : ↥A) = a :=
      Subtype.ext (psiPre_val H W W2 hD h4 a)
    rw [← ha, phiFun_spec H W W2 hD h4 ((normalizer (D : Set G)).inv_mem hg)
      (v := psiPre H W W2 hD h4 a) hv]
    rw [phiFun_spec H W W2 hD h4 hg
      (v := g⁻¹ * psiPre H W W2 hD h4 a * (g⁻¹)⁻¹)
      ((mem_normalizer_iff.1 (ThCyc.normalizer_D_le_normalizer_omega1 hD
        ((normalizer (D : Set G)).inv_mem hg)) _).1 hv)]
    apply Subtype.ext
    simp only
    congr 1
    group
  map_mul' := phiFun_mul_apply H W W2 hD h4 g hg

private noncomputable def phiHom (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) :
    ↥(normalizer (D : Set G)) →* MulAut ↥A where
  toFun g := phiAut H W W2 hD h4 (g : G) g.2
  map_one' := by
    apply MulEquiv.ext
    intro a
    exact phiFun_one H W W2 hD h4 a
  map_mul' g h := by
    apply MulEquiv.ext
    intro a
    exact phiFun_mul H W W2 hD h4 g.2 h.2 a

private noncomputable def Qsub (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) : Subgroup G :=
  (phiHom H W W2 hD h4).ker.map (normalizer (D : Set G)).subtype

private theorem mem_Q_iff (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {g : G} : g ∈ Qsub H W W2 hD h4 ↔
      ∃ hg : g ∈ normalizer (D : Set G), phiAut H W W2 hD h4 g hg = 1 := by
  constructor
  · intro hg
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hg
    exact ⟨m.2, by simpa [phiHom] using MonoidHom.mem_ker.1 hm⟩
  · rintro ⟨hg, hphi⟩
    exact Subgroup.mem_map.2 ⟨⟨g, hg⟩, by simpa [phiHom] using hphi, rfl⟩

private theorem phiAut_eq_one_iff (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {g : G}
    (hg : g ∈ normalizer (D : Set G)) : phiAut H W W2 hD h4 g hg = 1 ↔
      ∀ v ∈ omega1 D hD.comm, v⁻¹ * (g * v * g⁻¹) ∈ A := by
  constructor
  · intro h v hv
    have hvV := (mem_normalizer_iff.1 (ThCyc.normalizer_D_le_normalizer_omega1 hD hg) v).1 hv
    have heq : thV t (g * v * g⁻¹) = thV t v := by
      have hthis := congrArg (fun φ : MulAut ↥A =>
        ((φ ⟨thV t v, H.thV_mem_A W W2 hD hv⟩ : ↥A) : G)) h
      simp only [MulAut.one_apply] at hthis
      have hφ := congrArg (fun x : ↥A => (x : G)) (phiFun_spec H W W2 hD h4 hg hv)
      exact hφ.symm.trans hthis
    have h1 : thV t (v⁻¹ * (g * v * g⁻¹)) = 1 := by
      rw [H.thV_mul W W2 hD ((omega1 D hD.comm).inv_mem hv) hvV,
        thV_inv H W W2 hD hv, heq, inv_mul_cancel]
    exact (H.thV_eq_one_iff W W2 hD ((omega1 D hD.comm).mul_mem
      ((omega1 D hD.comm).inv_mem hv) hvV)).1 h1
  · intro h
    apply MulEquiv.ext
    intro a
    have hv := psiPre_mem H W W2 hD h4 a
    have hgeV : g * psiPre H W W2 hD h4 a * g⁻¹ ∈ omega1 D hD.comm :=
      (mem_normalizer_iff.1 (ThCyc.normalizer_D_le_normalizer_omega1 hD hg) _).1 hv
    have ha : (⟨thV t (psiPre H W W2 hD h4 a),
        H.thV_mem_A W W2 hD hv⟩ : ↥A) = a :=
      Subtype.ext (psiPre_val H W W2 hD h4 a)
    rw [← ha]
    change phiFun H W W2 hD h4 g hg
      ⟨thV t (psiPre H W W2 hD h4 a), H.thV_mem_A W W2 hD hv⟩ =
        (1 : MulAut ↥A) ⟨thV t (psiPre H W W2 hD h4 a),
          H.thV_mem_A W W2 hD hv⟩
    rw [phiFun_spec H W W2 hD h4 hg hv, MulAut.one_apply]
    have hmem := h (psiPre H W W2 hD h4 a) hv
    have h1 : thV t (g * psiPre H W W2 hD h4 a * g⁻¹) =
        thV t (psiPre H W W2 hD h4 a) := by
      have h2 : (psiPre H W W2 hD h4 a)⁻¹ *
          (g * psiPre H W W2 hD h4 a * g⁻¹) ∈ A := hmem
      have h3 : thV t ((psiPre H W W2 hD h4 a)⁻¹ *
          (g * psiPre H W W2 hD h4 a * g⁻¹)) = 1 :=
        (H.thV_eq_one_iff W W2 hD ((omega1 D hD.comm).mul_mem
          ((omega1 D hD.comm).inv_mem hv) hgeV)).2 h2
      rw [H.thV_mul W W2 hD ((omega1 D hD.comm).inv_mem hv) hgeV,
        thV_inv H W W2 hD hv] at h3
      calc thV t (g * psiPre H W W2 hD h4 a * g⁻¹)
          = thV t (psiPre H W W2 hD h4 a) *
              ((thV t (psiPre H W W2 hD h4 a))⁻¹ *
                thV t (g * psiPre H W W2 hD h4 a * g⁻¹)) := by group
        _ = thV t (psiPre H W W2 hD h4 a) * 1 := by rw [h3]
        _ = thV t (psiPre H W W2 hD h4 a) := mul_one _
    apply Subtype.ext
    exact h1

private theorem normInL_eq_inf : normInL L A = L ⊓ normalizer (A : Set G) := by
  ext n
  constructor
  · intro hn
    refine ⟨hn.1, mem_normalizer_iff.2 (mem_iff_conj_of_conj_le A (g := n) ?_)⟩
    intro a ha
    have h := (mem_normInL.1 ((normInL L A).inv_mem hn)).2 a ha
    simpa using h
  · rintro ⟨hnL, hnA⟩
    exact mem_normInL.2 ⟨hnL, fun a ha => (mem_normalizer_iff.1 hnA a).1 ha⟩

private theorem normInL_le_normalizer_D (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) : normInL L A ≤ normalizer (D : Set G) := by
  intro n hn
  have hnA : n ∈ normalizer (A : Set G) := by
    rw [normInL_eq_inf] at hn
    exact hn.2
  have h : n ∈ L ⊓ normalizer (D : Set G) := by
    rw [H.inf_normalizer_D_eq W W2 hD]
    exact ⟨hn.1, hnA⟩
  exact h.2

private theorem conj_mem_centralizer {n p : G} (hn : n ∈ normInL L A)
    (hp : p ∈ centralizer (A : Set G)) : n * p * n⁻¹ ∈ centralizer (A : Set G) := by
  refine mem_centralizer_iff.2 fun a ha => ?_
  have hna : n⁻¹ * a * n ∈ A := by
    have h := (mem_normInL.1 ((normInL L A).inv_mem hn)).2 a ha
    simpa using h
  have hc := mem_centralizer_iff.1 hp (n⁻¹ * a * n) hna
  calc a * (n * p * n⁻¹) = n * ((n⁻¹ * a * n) * p) * n⁻¹ := by group
    _ = n * (p * (n⁻¹ * a * n)) * n⁻¹ := by rw [hc]
    _ = (n * p * n⁻¹) * a := by group

private theorem normInL_le_normalizer_centralizer :
    normInL L A ≤ normalizer (centralizer (A : Set G) : Set G) := by
  intro n hn
  exact mem_normalizer_iff.2 (mem_iff_conj_of_conj_le (centralizer (A : Set G)) (g := n)
    (fun p hp => by
      have h := conj_mem_centralizer ((normInL L A).inv_mem hn) hp
      simpa using h))

private theorem B_le_normInL (W : ThLocalIn L S A B z) : B ≤ normInL L A := by
  intro x hx
  refine mem_normInL.2 ⟨W.B_le hx, fun a ha => ?_⟩
  have hc := (W.mem_B_iff x (W.B_le hx)).1 hx a ha
  have hxa : x * a * x⁻¹ = a := by
    calc x * a * x⁻¹ = (a * x) * x⁻¹ := by rw [hc]
      _ = a := by group
  rw [hxa]
  exact ha

private theorem B_le_normalizer_D (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) : B ≤ normalizer (D : Set G) :=
  (B_le_normInL W).trans (normInL_le_normalizer_D H W W2 hD)

private theorem mem_Q_action (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {g : G} :
    g ∈ Qsub H W W2 hD h4 ↔
      g ∈ normalizer (D : Set G) ∧
        ∀ v ∈ omega1 D hD.comm, v⁻¹ * (g * v * g⁻¹) ∈ A := by
  rw [mem_Q_iff H W W2 hD h4]
  constructor
  · rintro ⟨hg, hphi⟩
    exact ⟨hg, (phiAut_eq_one_iff H W W2 hD h4 hg).1 hphi⟩
  · rintro ⟨hg, hact⟩
    exact ⟨hg, (phiAut_eq_one_iff H W W2 hD h4 hg).2 hact⟩

private theorem Q_normal (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {m q : G} (hm : m ∈ normalizer (D : Set G))
    (hq : q ∈ Qsub H W W2 hD h4) : m * q * m⁻¹ ∈ Qsub H W W2 hD h4 := by
  obtain ⟨hqM, hqphi⟩ := (mem_Q_iff H W W2 hD h4).1 hq
  have hM : m * q * m⁻¹ ∈ normalizer (D : Set G) :=
    (normalizer (D : Set G)).mul_mem ((normalizer (D : Set G)).mul_mem hm hqM)
      ((normalizer (D : Set G)).inv_mem hm)
  refine (mem_Q_iff H W W2 hD h4).2 ⟨hM, ?_⟩
  have h1 : (⟨m * q * m⁻¹, hM⟩ : ↥(normalizer (D : Set G))) =
      (⟨m, hm⟩ : ↥(normalizer (D : Set G))) * (⟨q, hqM⟩ : ↥(normalizer (D : Set G))) *
        (⟨m, hm⟩ : ↥(normalizer (D : Set G)))⁻¹ := by ext; rfl
  have h2 : phiHom H W W2 hD h4 ⟨m * q * m⁻¹, hM⟩ = 1 := by
    rw [h1, map_mul, map_mul, map_inv]
    rw [show phiHom H W W2 hD h4 ⟨q, hqM⟩ = 1 by simpa [phiHom] using hqphi]
    simp
  simpa [phiHom] using h2

private theorem normInL_le_normalizer_Q (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) :
    normInL L A ≤ normalizer (Qsub H W W2 hD h4 : Set G) := by
  intro n hn
  have hnM := normInL_le_normalizer_D H W W2 hD hn
  refine mem_normalizer_iff.2 fun q => ⟨fun hq => ?_, fun hq => ?_⟩
  · exact Q_normal H W W2 hD h4 hnM hq
  · have hnM' := normInL_le_normalizer_D H W W2 hD ((normInL L A).inv_mem hn)
    have h := Q_normal H W W2 hD h4 hnM' hq
    convert h using 1
    group

private theorem normInL_le_normalizer_P (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) : normInL L A ≤ normalizer
      ((normalizer (D : Set G) ⊓ centralizer (A : Set G)) : Set G) := by
  have hconj : ∀ m ∈ normInL L A, ∀ p ∈ normalizer (D : Set G) ⊓ centralizer (A : Set G),
      m * p * m⁻¹ ∈ normalizer (D : Set G) ⊓ centralizer (A : Set G) := by
    intro m hm p hp
    have hmM := normInL_le_normalizer_D H W W2 hD hm
    refine ⟨(normalizer (D : Set G)).mul_mem
      ((normalizer (D : Set G)).mul_mem hmM hp.1) ((normalizer (D : Set G)).inv_mem hmM), ?_⟩
    exact conj_mem_centralizer hm hp.2
  intro n hn
  exact mem_normalizer_iff.2 (mem_iff_conj_of_conj_le
    (normalizer (D : Set G) ⊓ centralizer (A : Set G)) (g := n)
    (fun p hp => by
      have h := hconj n⁻¹ ((normInL L A).inv_mem hn) p hp
      simpa using h))

private theorem phiFun_normInL (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {l : G}
    (hl : l ∈ normInL L A) (hlM : l ∈ normalizer (D : Set G)) (a : ↥A) :
    phiFun H W W2 hD h4 l hlM a = ⟨l * (a : G) * l⁻¹, hl.2 a a.2⟩ := by
  apply Subtype.ext
  rw [phiFun_coe, H.thV_conj W W2 hD hl.1, psiPre_val]

private theorem phiAut_normInL (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) {l : G}
    (hl : l ∈ normInL L A) (hlM : l ∈ normalizer (D : Set G)) : phiAut H W W2 hD h4 l hlM =
      actA H W l (H.mem_normalizer_W5_of_mem_normInL W W2 hD hl) := by
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  change ((phiFun H W W2 hD h4 l hlM a : ↥A) : G) =
    ((actA H W l (H.mem_normalizer_W5_of_mem_normInL W W2 hD hl) a : ↥A) : G)
  rw [phiFun_normInL H W W2 hD h4 hl hlM a]
  rfl

private theorem P_inf_normInL_eq_B (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) :
    (normalizer (D : Set G) ⊓ centralizer (A : Set G)) ⊓ normInL L A = B := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨⟨-, hxC⟩, hxN⟩
    exact (W.mem_B_iff x hxN.1).2 fun a ha => (mem_centralizer_iff.1 hxC a ha).symm
  · intro x hx
    have hxN := B_le_normInL W hx
    exact ⟨⟨normInL_le_normalizer_D H W W2 hD hxN,
      mem_centralizer_iff.2 fun a ha => ((W.mem_B_iff x hxN.1).1 hx a ha).symm⟩, hxN⟩

private theorem Q_inf_normInL_eq_B (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) :
    Qsub H W W2 hD h4 ⊓ normInL L A = B := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxQ, hxN⟩
    have hxM := normInL_le_normalizer_D H W W2 hD hxN
    have hphi : phiAut H W W2 hD h4 x hxM = 1 := (mem_Q_iff H W W2 hD h4).1 hxQ |>.2
    have hxact : actA H W x (H.mem_normalizer_W5_of_mem_normInL W W2 hD hxN) = 1 := by
      rw [← phiAut_normInL H W W2 hD h4 hxN hxM]
      exact hphi
    refine (W.mem_B_iff x hxN.1).2 fun a ha => ?_
    have hconj := congrArg (fun ψ : MulAut ↥A => ((ψ ⟨a, ha⟩ : ↥A) : G)) hxact
    have hxa : x * a * x⁻¹ = a := by
      simpa [actA, MulAut.one_apply] using hconj
    calc x * a = (x * a * x⁻¹) * x := by group
      _ = a * x := by rw [hxa]
  · intro x hx
    have hxN := B_le_normInL W hx
    have hxM := normInL_le_normalizer_D H W W2 hD hxN
    refine ⟨(mem_Q_iff H W W2 hD h4).2 ⟨hxM, ?_⟩, hxN⟩
    rw [phiAut_normInL H W W2 hD h4 hxN hxM]
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    have hc := (W.mem_B_iff x hxN.1).1 hx a a.2
    dsimp [actA, MulAut.one_apply]
    calc x * (a : G) * x⁻¹ = ((a : G) * x) * x⁻¹ := by rw [hc]
      _ = (a : G) := by group

private noncomputable def phiN (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) :
    ↥(normInL L A) →* MulAut ↥A :=
  (phiHom H W W2 hD h4).comp
    (Subgroup.inclusion (normInL_le_normalizer_D H W W2 hD))

private theorem phiN_apply (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) (x : ↥(normInL L A)) : phiN H W W2 hD h4 x =
      phiAut H W W2 hD h4 (x : G) (normInL_le_normalizer_D H W W2 hD x.2) := rfl

private theorem phiN_surj (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) : Function.Surjective (phiN H W W2 hD h4) := by
  intro φ
  classical
  let f : G → G := fun a => if ha : a ∈ A then ((φ ⟨a, ha⟩ : ↥A) : G) else 1
  have hfA : ∀ a ∈ A, f a ∈ A := by
    intro a ha
    dsimp [f]
    rw [dif_pos ha]
    exact (φ ⟨a, ha⟩).2
  have hfmul : ∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b := by
    intro a ha b hb
    dsimp [f]
    rw [dif_pos (A.mul_mem ha hb), dif_pos ha, dif_pos hb]
    exact congrArg (fun x : ↥A => (x : G)) (φ.map_mul ⟨a, ha⟩ ⟨b, hb⟩)
  have hfinj : ∀ a ∈ A, ∀ b ∈ A, f a = f b → a = b := by
    intro a ha b hb hab
    dsimp [f] at hab
    rw [dif_pos ha, dif_pos hb] at hab
    exact congrArg (fun x : ↥A => (x : G)) (φ.injective (Subtype.ext hab))
  obtain ⟨l, hlL, hl⟩ := W.surj f hfA hfmul hfinj
  have hlA : ∀ a ∈ A, l * a * l⁻¹ ∈ A := fun a ha => by
    rw [hl a ha]
    exact hfA a ha
  have hlN : l ∈ normInL L A := mem_normInL.2 ⟨hlL, hlA⟩
  refine ⟨⟨l, hlN⟩, ?_⟩
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  rw [phiN_apply, phiAut_normInL H W W2 hD h4 hlN
    (normInL_le_normalizer_D H W W2 hD hlN)]
  dsimp [actA]
  rw [hl (a : G) a.2]
  simp [f, a.2]

private theorem phiN_ker (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) :
    (phiN H W W2 hD h4).ker = B.subgroupOf (normInL L A) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have hxM := normInL_le_normalizer_D H W W2 hD x.2
    have hphi : phiAut H W W2 hD h4 (x : G) hxM = 1 := by
      simpa [phiN, phiHom] using h
    have hxact : actA H W (x : G)
        (H.mem_normalizer_W5_of_mem_normInL W W2 hD x.2) = 1 := by
      rw [← phiAut_normInL H W W2 hD h4 x.2 hxM]
      exact hphi
    refine (W.mem_B_iff (x : G) x.2.1).2 fun a ha => ?_
    have hconj := congrArg (fun ψ : MulAut ↥A => ((ψ ⟨a, ha⟩ : ↥A) : G)) hxact
    have hxa : (x : G) * a * (x : G)⁻¹ = a := by
      simpa [actA, MulAut.one_apply] using hconj
    calc (x : G) * a = ((x : G) * a * (x : G)⁻¹) * (x : G) := by group
      _ = a * (x : G) := by rw [hxa]
  · intro hxB
    have hxN := B_le_normInL W hxB
    have hxM := normInL_le_normalizer_D H W W2 hD hxN
    have hxact : actA H W (x : G)
        (H.mem_normalizer_W5_of_mem_normInL W W2 hD x.2) = 1 := by
      apply MulEquiv.ext
      intro a
      apply Subtype.ext
      have hc := (W.mem_B_iff (x : G) x.2.1).1 hxB a a.2
      dsimp [actA, MulAut.one_apply]
      calc (x : G) * (a : G) * (x : G)⁻¹ = ((a : G) * (x : G)) * (x : G)⁻¹ := by rw [hc]
        _ = (a : G) := by group
    have hphi : phiAut H W W2 hD h4 (x : G) hxM = 1 := by
      rw [phiAut_normInL H W W2 hD h4 hxN hxM]
      exact hxact
    simpa [phiN, phiHom] using hphi

private theorem card_normInL_eq (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) :
    Nat.card (normInL L A) = Nat.card B * Nat.card (MulAut ↥A) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (phiN H W W2 hD h4).ker
  have h2 : Nat.card (↥(normInL L A) ⧸ (phiN H W W2 hD h4).ker) =
      Nat.card (MulAut ↥A) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (phiN H W W2 hD h4)).toEquiv]
    have htop : (phiN H W W2 hD h4).range = ⊤ :=
      MonoidHom.range_eq_top.2 (phiN_surj H W W2 hD h4)
    rw [htop]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  have h3 : Nat.card (phiN H W W2 hD h4).ker = Nat.card B := by
    rw [phiN_ker H W W2 hD h4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (B_le_normInL W)).toEquiv
  rw [h1, h2, h3, mul_comm]

private theorem card_inf_centralizer_t_eq (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) :
    Nat.card ↥(normalizer (D : Set G) ⊓ centralizer ({t} : Set G)) =
      2 ^ 10 * Nat.card (MulAut ↥A) := by
  rw [H.normalizer_D_inf_centralizer_t W W2 hD, ← normInL_eq_inf]
  have hcomm : ∀ x ∈ normInL L A, ∀ y ∈ zpowers t, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((show Commute x t from (H.comm_of_mem_L hx.1).symm).zpow_right k).eq
  have hdisj : normInL L A ⊓ zpowers t = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxN, hxt⟩ := hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxt
    rcases zpow_eq_one_or_self H.sq_t k with h | h
    · rw [h]
      exact one_mem _
    · exfalso
      rw [h] at hxN
      have htLR : t ∈ L ⊓ R := ⟨hxN.1, H.mem⟩
      rw [disjoint_iff.1 H.disjoint, mem_bot] at htLR
      have ht1 : t = 1 := htLR
      have h2 := H.order_two
      rw [ht1, orderOf_one] at h2
      omega
  rw [natCard_sup_of_commute hcomm hdisj, Nat.card_zpowers, H.order_two,
    card_normInL_eq H W W2 hD h4, W.B_card]
  ring

private theorem normalizer_D_eq_P_sup_normInL (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) :
    normalizer (D : Set G) =
      (normalizer (D : Set G) ⊓ centralizer (A : Set G)) ⊔ normInL L A := by
  refine le_antisymm ?_ (sup_le inf_le_left (normInL_le_normalizer_D H W W2 hD))
  intro g hg
  have hgA : g ∈ normalizer (A : Set G) :=
    H.normalizer_D_le_normalizer_A W W2 hD h4 hg
  have hgSup : g ∈ centralizer (A : Set G) ⊔ normInL L A := by
    rw [normInL_eq_inf, ← ThCyc.normalizer_A_eq_sup W]
    exact hgA
  have hnormC : normInL L A ≤ normalizer (centralizer (A : Set G) : Set G) :=
    normInL_le_normalizer_centralizer
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left
    (centralizer (A : Set G)) (normInL L A) hnormC] at hgSup
  obtain ⟨c, hc, n, hn, hcn⟩ := hgSup
  have hcM : c ∈ normalizer (D : Set G) := by
    have hgn : g * n⁻¹ = c := by rw [← hcn]; group
    rw [← hgn]
    exact (normalizer (D : Set G)).mul_mem hg ((normalizer (D : Set G)).inv_mem
      (normInL_le_normalizer_D H W W2 hD hn))
  rw [← hcn]
  exact mul_mem_sup ⟨hcM, hc⟩ hn

private theorem normalizer_D_eq_Q_sup_normInL (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) :
    normalizer (D : Set G) = Qsub H W W2 hD h4 ⊔ normInL L A := by
  refine le_antisymm ?_ ?_
  · intro g hg
    classical
    let φ : MulAut ↥A := phiAut H W W2 hD h4 g hg
    let f : G → G := fun a => if ha : a ∈ A then ((φ ⟨a, ha⟩ : ↥A) : G) else 1
    have hfA : ∀ a ∈ A, f a ∈ A := by
      intro a ha
      dsimp [f]
      rw [dif_pos ha]
      exact (φ ⟨a, ha⟩).2
    have hfmul : ∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b := by
      intro a ha b hb
      dsimp [f]
      rw [dif_pos (A.mul_mem ha hb), dif_pos ha, dif_pos hb]
      exact congrArg (fun x : ↥A => (x : G)) (φ.map_mul ⟨a, ha⟩ ⟨b, hb⟩)
    have hfinj : ∀ a ∈ A, ∀ b ∈ A, f a = f b → a = b := by
      intro a ha b hb hab
      dsimp [f] at hab
      rw [dif_pos ha, dif_pos hb] at hab
      exact congrArg (fun x : ↥A => (x : G)) (φ.injective (Subtype.ext hab))
    obtain ⟨l, hlL, hl⟩ := W.surj f hfA hfmul hfinj
    have hlA : ∀ a ∈ A, l * a * l⁻¹ ∈ A := fun a ha => by
      rw [hl a ha]
      exact hfA a ha
    have hlN : l ∈ normInL L A := mem_normInL.2 ⟨hlL, hlA⟩
    have hlM := normInL_le_normalizer_D H W W2 hD hlN
    have hphil : phiAut H W W2 hD h4 l hlM = φ := by
      apply MulEquiv.ext
      intro a
      apply Subtype.ext
      rw [phiAut_normInL H W W2 hD h4 hlN hlM]
      dsimp [actA]
      rw [hl (a : G) a.2]
      simp [f, a.2]
    have hqM : g * l⁻¹ ∈ normalizer (D : Set G) :=
      (normalizer (D : Set G)).mul_mem hg ((normalizer (D : Set G)).inv_mem hlM)
    have hqphi : phiAut H W W2 hD h4 (g * l⁻¹) hqM = 1 := by
      have h1 : (⟨g * l⁻¹, hqM⟩ : ↥(normalizer (D : Set G))) =
          (⟨g, hg⟩ : ↥(normalizer (D : Set G))) *
            (⟨l, hlM⟩ : ↥(normalizer (D : Set G)))⁻¹ := by ext; rfl
      have h2 : phiHom H W W2 hD h4 ⟨g * l⁻¹, hqM⟩ = 1 := by
        rw [h1, map_mul, map_inv]
        rw [show phiHom H W W2 hD h4 ⟨l, hlM⟩ = φ by exact hphil]
        rw [show phiHom H W W2 hD h4 ⟨g, hg⟩ = φ by rfl]
        simp
      simpa [phiHom] using h2
    have hq : g * l⁻¹ ∈ Qsub H W W2 hD h4 :=
      (mem_Q_iff H W W2 hD h4).2 ⟨hqM, hqphi⟩
    have e : g = (g * l⁻¹) * l := by group
    rw [e]
    exact mul_mem_sup hq hlN
  · exact sup_le (Subgroup.map_subtype_le _) (normInL_le_normalizer_D H W W2 hD)

private theorem B_le_Q (H : ThCyc G L R t) (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b)
    (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) :
    B ≤ Qsub H W W2 hD h4 := by
  intro x hx
  refine (mem_Q_action H W W2 hD h4).2 ⟨B_le_normalizer_D H W W2 hD hx, ?_⟩
  intro v hv
  have hcomm := H.comm_omega1_of_mem_B W W2 hD hb hx hv
  have h : v⁻¹ * (x * v * x⁻¹) = 1 := by rw [hcomm, inv_mul_cancel]
  rw [h]
  exact A.one_mem

private noncomputable def mulAutEquivGL4A (W : ThLocalIn L S A B z) :
    MulAut ↥A ≃* GL (Fin 4) (ZMod 2) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : ↥A ≃* Multiplicative (Fin 4 → ZMod 2) :=
    Classical.choice (CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
      (p := 2) (W := ↥A) (fun a b => Subtype.ext (W.A_comm a a.2 b b.2))
      (fun a => Subtype.ext (by simpa using W.A_sq a a.2)) (n := 4) (by
        rw [W.A_card]; norm_num))
  exact (MulAut.congr e).trans (CFSG.SectionRank.Ccomm.mulAutEquivGL (p := 2) 4)

theorem ThLocalIn.isSimpleGroup_mulAut_A (W : ThLocalIn L S A B z) :
    IsSimpleGroup (MulAut ↥A) := by
  haveI : IsSimpleGroup (GL (Fin 4) (ZMod 2)) :=
    CFSG.LargeExtraspecial.S45Q.isSimpleGroup_GL_zmod_two (by norm_num)
  exact (mulAutEquivGL4A W).isSimpleGroup

theorem ThLocalIn.card_mulAut_A (W : ThLocalIn L S A B z) :
    Nat.card (MulAut ↥A) = 20160 := by
  rw [Nat.card_congr (mulAutEquivGL4A W).toEquiv,
    CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2) (n := 4)]
  decide

private theorem normal_subgroup_dichotomy (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {X : Subgroup G} (hXM : X ≤ normalizer (D : Set G))
    (hQX : Qsub H W W2 hD h4 ≤ X)
    (hXnorm : ∀ m ∈ normalizer (D : Set G), ∀ x ∈ X, m * x * m⁻¹ ∈ X) :
    X = Qsub H W W2 hD h4 ∨ X = normalizer (D : Set G) := by
  let N := normInL L A
  let Y : Subgroup ↥N := X.subgroupOf N
  have hB_le_Y : B.subgroupOf N ≤ Y := by
    intro b hbB
    rw [Subgroup.mem_subgroupOf] at hbB ⊢
    exact hQX (B_le_Q H W W2 hD h4 hb hbB)
  have hYnorm : ∀ n : ↥N, ∀ y ∈ Y, n * y * n⁻¹ ∈ Y := by
    intro n y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    simpa using hXnorm (n : G) (normInL_le_normalizer_D H W W2 hD n.2) (y : G) hy
  have hnormal_image : (Subgroup.map (phiN H W W2 hD h4) Y).Normal := by
    refine { conj_mem := ?_ }
    intro y hy m
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨m', rfl⟩ := phiN_surj H W W2 hD h4 m
    refine Subgroup.mem_map.2 ⟨m' * n * m'⁻¹, hYnorm m' n hn, ?_⟩
    rw [map_mul, map_mul, map_inv]
  haveI : IsSimpleGroup (MulAut ↥A) := ThLocalIn.isSimpleGroup_mulAut_A W
  haveI := hnormal_image
  rcases Subgroup.Normal.eq_bot_or_eq_top
    (Subgroup.map (phiN H W W2 hD h4) Y) with hbot | htop
  · left
    have hYleB : Y ≤ B.subgroupOf N := by
      intro y hy
      have himage : phiN H W W2 hD h4 y ∈
          Subgroup.map (phiN H W W2 hD h4) Y :=
        Subgroup.mem_map.2 ⟨y, hy, rfl⟩
      rw [hbot] at himage
      have h1 : phiN H W W2 hD h4 y = 1 := Subgroup.mem_bot.1 himage
      have h2 : y ∈ (phiN H W W2 hD h4).ker := MonoidHom.mem_ker.2 h1
      rwa [phiN_ker H W W2 hD h4] at h2
    have hXinf_le_B : X ⊓ N ≤ B := by
      intro x hx
      have hxY : (⟨x, hx.2⟩ : ↥N) ∈ Y := by
        rw [Subgroup.mem_subgroupOf]
        exact hx.1
      have h := hYleB hxY
      rwa [Subgroup.mem_subgroupOf] at h
    refine le_antisymm ?_ hQX
    intro x hx
    have hxM : x ∈ normalizer (D : Set G) := hXM hx
    have hxQN : x ∈ Qsub H W W2 hD h4 ⊔ N := by
      rw [← normalizer_D_eq_Q_sup_normInL H W W2 hD h4]
      exact hxM
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left
      (Qsub H W W2 hD h4) N (normInL_le_normalizer_Q H W W2 hD h4)] at hxQN
    obtain ⟨q, hq, n, hn, hqn⟩ := hxQN
    have hnX : n ∈ X := by
      have e : n = q⁻¹ * x := by rw [← hqn]; group
      rw [e]
      exact X.mul_mem (X.inv_mem (hQX hq)) hx
    have hnB : n ∈ B := hXinf_le_B ⟨hnX, hn⟩
    rw [← hqn]
    exact (Qsub H W W2 hD h4).mul_mem hq (B_le_Q H W W2 hD h4 hb hnB)
  · right
    have hNleX : N ≤ X := by
      intro n hn
      have hmem : phiN H W W2 hD h4 ⟨n, hn⟩ ∈
          Subgroup.map (phiN H W W2 hD h4) Y := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨y, hyY, hyeq⟩ := Subgroup.mem_map.1 hmem
      have hyX : (y : G) ∈ X := by
        rw [Subgroup.mem_subgroupOf] at hyY
        exact hyY
      have hker : (y : G)⁻¹ * n ∈ B := by
        have hmemker : (⟨(y : G)⁻¹ * n, N.mul_mem (N.inv_mem y.2) hn⟩ : ↥N) ∈
            (phiN H W W2 hD h4).ker := by
          rw [MonoidHom.mem_ker]
          have h2 : (⟨(y : G)⁻¹ * n, N.mul_mem (N.inv_mem y.2) hn⟩ : ↥N) =
              y⁻¹ * ⟨n, hn⟩ := by ext; rfl
          rw [h2, map_mul, map_inv, hyeq]
          simp
        rw [phiN_ker H W W2 hD h4] at hmemker
        rwa [Subgroup.mem_subgroupOf] at hmemker
      have e : n = (y : G) * ((y : G)⁻¹ * n) := by group
      rw [e]
      exact X.mul_mem hyX (hQX (B_le_Q H W W2 hD h4 hb hker))
    have hMleX : normalizer (D : Set G) ≤ X := by
      rw [normalizer_D_eq_Q_sup_normInL H W W2 hD h4]
      exact sup_le hQX hNleX
    exact le_antisymm hXM hMleX

theorem ThCyc.conj_mul_inv_mem_A_of_mem_normalizer_D (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {c : G} (hcM : c ∈ normalizer (D : Set G))
    (hcA : ∀ a ∈ A, c * a * c⁻¹ = a) {v : G} (hv : v ∈ omega1 D hD.comm) :
    v⁻¹ * (c * v * c⁻¹) ∈ A := by
  classical
  let M := normalizer (D : Set G)
  let P : Subgroup G := M ⊓ centralizer (A : Set G)
  let Q : Subgroup G := Qsub H W W2 hD h4
  have hA_le_L : A ≤ L := fun a ha => W.S_le ((W.mem_A_iff a).1 ha).1
  have htM : t ∈ M := le_normalizer_of_conj_mem hD.norm (H.t_mem_normalizer W W2 hD)
  have htP : t ∈ P := ⟨htM, mem_centralizer_iff.2 fun a ha =>
    (H.comm_of_mem_L (hA_le_L ha)).symm⟩
  have htQ : t ∈ Q := by
    refine (mem_Q_action H W W2 hD h4).2 ⟨htM, ?_⟩
    intro w hw
    have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right (H.omega1_mul_self W W2 hD hw)
    rw [hw']
    exact H.thV_mem_A W W2 hD hw
  have hcP : c ∈ P := ⟨hcM, mem_centralizer_iff.2 fun a ha => by
    calc a * c = (c * a * c⁻¹) * c := by rw [hcA a ha]
      _ = c * a := by group⟩
  have hPM : P ≤ M := inf_le_left
  have hQM : Q ≤ M := by
    intro x hx
    obtain ⟨m, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact m.2
  have hPnorm : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P := by
    intro m hm p hp
    refine ⟨M.mul_mem (M.mul_mem hm hp.1) (M.inv_mem hm), ?_⟩
    have hmA : m ∈ normalizer (A : Set G) := H.normalizer_D_le_normalizer_A W W2 hD h4 hm
    refine mem_centralizer_iff.2 fun a ha => ?_
    have hma : m⁻¹ * a * m ∈ A := by
      have h := (mem_normalizer_iff.1 ((normalizer (A : Set G)).inv_mem hmA) a).1 ha
      simpa using h
    have hc := mem_centralizer_iff.1 hp.2 (m⁻¹ * a * m) hma
    calc a * (m * p * m⁻¹) = m * ((m⁻¹ * a * m) * p) * m⁻¹ := by group
      _ = m * (p * (m⁻¹ * a * m)) * m⁻¹ := by rw [hc]
      _ = (m * p * m⁻¹) * a := by group
  have hPQle : P ≤ Q := by
    by_contra hnot
    have hXneQ : P ⊔ Q ≠ Q := by
      intro h
      exact hnot (le_trans le_sup_left (le_of_eq h))
    have hXnorm : ∀ m ∈ M, ∀ x ∈ P ⊔ Q, m * x * m⁻¹ ∈ P ⊔ Q := by
      intro m hm x hx
      have hmapP : P.map (MulAut.conj m).toMonoidHom ≤ P := by
        rintro _ ⟨p, hp, rfl⟩
        exact hPnorm m hm p hp
      have hmapQ : Q.map (MulAut.conj m).toMonoidHom ≤ Q := by
        rintro _ ⟨q, hq, rfl⟩
        exact Q_normal H W W2 hD h4 hm hq
      have hmapX : (P ⊔ Q).map (MulAut.conj m).toMonoidHom ≤ P ⊔ Q := by
        rw [Subgroup.map_sup]
        exact sup_le (hmapP.trans le_sup_left) (hmapQ.trans le_sup_right)
      exact hmapX (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
    have hX : P ⊔ Q = M := by
      rcases normal_subgroup_dichotomy H W W2 hD h4 hb (sup_le hPM hQM)
        le_sup_right hXnorm with h | h
      · exact absurd h hXneQ
      · exact h
    let bcard := Nat.card B
    let x := Nat.card (MulAut ↥A)
    let pcard := Nat.card P
    let qcard := Nat.card Q
    let rcard := Nat.card ↥(P ⊓ Q)
    let ccard := Nat.card ↥(M ⊓ centralizer ({t} : Set G))
    have hx : x = 20160 := ThLocalIn.card_mulAut_A W
    have hbcard : bcard = 2 ^ 9 := W.B_card
    have hn : Nat.card (normInL L A) = bcard * x := card_normInL_eq H W W2 hD h4
    have hccard : ccard = 2 ^ 10 * x := card_inf_centralizer_t_eq H W W2 hD h4
    have hcardNP : Nat.card M * bcard = pcard * Nat.card (normInL L A) := by
      have h := SylowEnd.card_sup_mul_card_inf (H := normInL L A) (K := P)
        (normInL_le_normalizer_P H W W2 hD)
      have hsup : normInL L A ⊔ P = M := by
        rw [sup_comm]
        exact (normalizer_D_eq_P_sup_normInL H W W2 hD h4).symm
      have hinf : normInL L A ⊓ P = B := by
        rw [inf_comm, P_inf_normInL_eq_B H W W2 hD]
      rw [hsup, hinf] at h
      simpa [M, bcard, pcard, mul_comm] using h
    have hcardNQ : Nat.card M * bcard = qcard * Nat.card (normInL L A) := by
      have h := SylowEnd.card_sup_mul_card_inf (H := normInL L A) (K := Q)
        (normInL_le_normalizer_Q H W W2 hD h4)
      have hsup : normInL L A ⊔ Q = M := by
        rw [sup_comm]
        exact (normalizer_D_eq_Q_sup_normInL H W W2 hD h4).symm
      have hinf : normInL L A ⊓ Q = B := by
        rw [inf_comm, Q_inf_normInL_eq_B H W W2 hD h4]
      rw [hsup, hinf] at h
      simpa [M, bcard, qcard, mul_comm] using h
    have hcardPQ : Nat.card M * rcard = pcard * qcard := by
      have hPnormQ : P ≤ normalizer (Q : Set G) := by
        intro p pp
        refine mem_normalizer_iff.2 fun q => ⟨fun qq => ?_, fun qq => ?_⟩
        · exact Q_normal H W W2 hD h4 pp.1 qq
        · have h := Q_normal H W W2 hD h4 (P.inv_mem pp).1 qq
          convert h using 1
          group
      have h := SylowEnd.card_sup_mul_card_inf (H := P) (K := Q) hPnormQ
      rw [hX] at h
      simpa [M, pcard, qcard, rcard] using h
    have hbpos : 0 < bcard := Nat.card_pos
    have hm : Nat.card M = pcard * x := by
      have h1 : Nat.card M * bcard = (pcard * x) * bcard := by
        rw [hcardNP, hn, mul_assoc, mul_comm bcard x, ← mul_assoc]
      exact Nat.mul_right_cancel hbpos h1
    have hm' : Nat.card M = qcard * x := by
      have h1 : Nat.card M * bcard = (qcard * x) * bcard := by
        rw [hcardNQ, hn, mul_assoc, mul_comm bcard x, ← mul_assoc]
      exact Nat.mul_right_cancel hbpos h1
    have hxpos : 0 < x := by rw [hx]; norm_num
    have hrx : rcard * x ^ 2 = Nat.card M := by
      have h1 : Nat.card M * rcard = pcard * qcard := hcardPQ
      have h2 : (pcard * x) * (qcard * x) = Nat.card M * Nat.card M := by
        rw [← hm, ← hm']
      have h3 : Nat.card M * rcard * x * x = Nat.card M * Nat.card M := by
        calc Nat.card M * rcard * x * x = (pcard * qcard) * x * x := by rw [h1]
          _ = (pcard * x) * (qcard * x) := by ring
          _ = Nat.card M * Nat.card M := h2
      have h4 : rcard * x * x = Nat.card M := by
        have h5 : Nat.card M * (rcard * x * x) = Nat.card M * Nat.card M := by
          calc Nat.card M * (rcard * x * x) = Nat.card M * rcard * x * x := by ring
            _ = Nat.card M * Nat.card M := h3
        exact Nat.mul_left_cancel (Nat.card_pos (α := ↥M)) h5
      simpa [pow_two, mul_assoc] using h4
    let tM : ↥M := ⟨t, htM⟩
    let T : Set ↥M := MulAction.orbit (ConjAct ↥M) tM
    have hCT : Nat.card (Subgroup.centralizer ({tM} : Set ↥M)) = ccard := by
      have hEq : Subgroup.centralizer ({tM} : Set ↥M) =
          (M ⊓ centralizer ({t} : Set G)).subgroupOf M := by
        ext x
        rw [Subgroup.mem_subgroupOf]
        constructor
        · intro hx
          refine ⟨x.2, mem_centralizer_singleton_iff.2 ?_⟩
          exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 hx)
        · rintro ⟨-, hx⟩
          exact mem_centralizer_singleton_iff.2
            (Subtype.ext (mem_centralizer_singleton_iff.1 hx))
      rw [hEq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : M ⊓ _ ≤ M)).toEquiv
    have hclass : Nat.card T * ccard = Nat.card ↥M := by
      letI : Fintype ↥M := Fintype.ofFinite _
      have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct ↥M) tM
      have h' : Nat.card T * Nat.card ↥(MulAction.stabilizer (ConjAct ↥M) tM) =
          Nat.card (ConjAct ↥M) := by
        simpa only [Nat.card_eq_fintype_card] using h
      rw [← Subgroup.nat_card_centralizer_nat_card_stabilizer, hCT] at h'
      rw [show Nat.card (ConjAct ↥M) = Nat.card ↥M from
        Nat.card_congr ConjAct.ofConjAct.toEquiv] at h'
      exact h'
    have hTle : Nat.card T ≤ rcard := by
      let cOf : T → ConjAct ↥M := fun y => Classical.choose (MulAction.mem_orbit_iff.1 y.2)
      have hcOf : ∀ y : T, cOf y • tM = y.1 := fun y =>
        Classical.choose_spec (MulAction.mem_orbit_iff.1 y.2)
      let mOf : T → ↥M := fun y => ConjAct.ofConjAct (cOf y)
      have hmval : ∀ y : T, (mOf y : G) * t * (mOf y : G)⁻¹ = (y.1 : G) := by
        intro y
        have h := congrArg Subtype.val (hcOf y)
        simpa [mOf, tM, ConjAct.smul_def] using h
      let f : T → ↥(P ⊓ Q) := fun y => ⟨(y.1 : G), by
        refine ⟨?_, ?_⟩
        · rw [← hmval y]
          exact hPnorm (mOf y) (mOf y).2 t htP
        · rw [← hmval y]
          exact Q_normal H W W2 hD h4 (mOf y).2 htQ⟩
      have hf : Function.Injective f := by
        intro y z hyz
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun w : ↥(P ⊓ Q) => (w : G)) hyz
      exact Nat.card_le_card_of_injective f hf
    have hmain : rcard * x = 2 ^ 10 * Nat.card T := by
      have h1 : rcard * x ^ 2 = Nat.card T * ccard := by
        rw [hrx, ← hclass]
      rw [hccard] at h1
      have h2 : rcard * x * x = (2 ^ 10 * Nat.card T) * x := by
        calc rcard * x * x = rcard * x ^ 2 := by ring
          _ = Nat.card T * (2 ^ 10 * x) := h1
          _ = (2 ^ 10 * Nat.card T) * x := by ring
      exact Nat.mul_right_cancel hxpos h2
    have hle : rcard * x ≤ 2 ^ 10 * rcard := by
      calc rcard * x = 2 ^ 10 * Nat.card T := hmain
        _ ≤ 2 ^ 10 * rcard := Nat.mul_le_mul_left _ hTle
    have hrpos : 0 < rcard := Nat.card_pos (α := ↥(P ⊓ Q))
    have hxle : x ≤ 2 ^ 10 := by
      have h := Nat.le_of_mul_le_mul_left (by simpa [mul_comm] using hle) hrpos
      exact h
    have : 20160 ≤ 2 ^ 10 := by rw [← hx]; exact hxle
    norm_num at this
  exact (mem_Q_action H W W2 hD h4).1 (hPQle hcP) |>.2 v hv

end CFSG.EvenSporadicStandard.ThStd
