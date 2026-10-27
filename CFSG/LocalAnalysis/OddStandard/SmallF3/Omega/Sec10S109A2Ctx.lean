module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109A1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109A2Gen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L104Odd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TK0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Comb

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure Sec10A2Ctx (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G)
    (K1 K2 : Subgroup G) (g : G) : Prop extends Sec10Ctx G t L S z K1 K2 where
  norm : g ∈ normalizer (S : Set G)
  not_M : g ∉ secM t S L
  two : IsPGroup 2 (zpowers g)
  swap_t : g⁻¹ * t * g = t * z
  fix_z : g⁻¹ * z * g = z

variable [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} {g : G}

theorem sec10A2_conj_tz (hb : Asc82Basic10) (hctx : Sec10A2Ctx G t L S z K1 K2 g) :
    g * z = z * g ∧ g * z * g⁻¹ = z ∧ g * t * g⁻¹ = t * z := by
  obtain ⟨-, hz2, -, -, -, -⟩ := sec10D_basic hb hctx.toSec10Ctx
  have hgz : g * z = z * g := by
    calc g * z = g * (g⁻¹ * z * g) := by rw [hctx.fix_z]
      _ = z * g := by group
  have e1 : g * z * g⁻¹ = z := by
    calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [hgz]
      _ = z := by group
  refine ⟨hgz, e1, ?_⟩
  have e2 : t = (g * t * g⁻¹) * z := by
    calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = g * (t * z) * g⁻¹ := by rw [hctx.swap_t]
      _ = (g * t * g⁻¹) * (g * z * g⁻¹) := by group
      _ = (g * t * g⁻¹) * z := by rw [e1]
  calc g * t * g⁻¹ = (g * t * g⁻¹) * (z * z) := by rw [hz2, mul_one]
    _ = ((g * t * g⁻¹) * z) * z := by group
    _ = t * z := by rw [← e2]

theorem sec10A2_sq_mem_S (hb : Asc82Basic10) (hctx : Sec10A2Ctx G t L S z K1 K2 g) :
    g * g ∈ S := by
  obtain ⟨-, hz2, -, -, -, -⟩ := sec10D_basic hb hctx.toSec10Ctx
  obtain ⟨hgz, e1, e3⟩ := sec10A2_conj_tz hb hctx
  have hgg : g * g * t * (g * g)⁻¹ = t := by
    calc g * g * t * (g * g)⁻¹ = g * (g * t * g⁻¹) * g⁻¹ := by group
      _ = g * (t * z) * g⁻¹ := by rw [e3]
      _ = (g * t * g⁻¹) * (g * z * g⁻¹) := by group
      _ = (t * z) * z := by rw [e3, e1]
      _ = t := by rw [mul_assoc, hz2, mul_one]
  have hggC : g * g ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * g * t = (g * g * t * (g * g)⁻¹) * (g * g) := by group
      _ = t * (g * g) := by rw [hgg]
  have hmem : g * g ∈ zpowers g := Subgroup.mul_mem _ (Subgroup.mem_zpowers g)
    (Subgroup.mem_zpowers g)
  have hgg2 : IsPGroup 2 ↥(zpowers (g * g)) :=
    hctx.two.to_le (Subgroup.zpowers_le.mpr hmem)
  have hggN : g * g ∈ normalizer (S : Set G) := (normalizer (S : Set G)).mul_mem hctx.norm hctx.norm
  have hQ2 : IsPGroup 2 ↥(S ⊔ zpowers (g * g)) :=
    IsPGroup.to_sup_of_normal_left' hctx.sylow.2.1 hgg2 (Subgroup.zpowers_le.mpr hggN)
  have hQC : S ⊔ zpowers (g * g) ≤ centralizer ({t} : Set G) :=
    sup_le hctx.sylow.1 (Subgroup.zpowers_le.mpr hggC)
  have heq := hctx.sylow.eq_of_le hQC hQ2 le_sup_left
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem sec10A2_T_pgroup (hctx : Sec10A2Ctx G t L S z K1 K2 g) :
    IsPGroup 2 ↥(S ⊔ zpowers g) :=
  IsPGroup.to_sup_of_normal_left' hctx.sylow.2.1 hctx.two (Subgroup.zpowers_le.mpr hctx.norm)

theorem sec10A2_T_cases (hb : Asc82Basic10) (hctx : Sec10A2Ctx G t L S z K1 K2 g) :
    ∀ y ∈ S ⊔ zpowers g, y ∈ S ∨ g⁻¹ * y ∈ S :=
  sec10A2_mem_sup_zpowers hctx.norm (sec10A2_sq_mem_S hb hctx)

theorem sec10A2_T_le_hatCent (hb : Asc82Basic10) (hctx : Sec10A2Ctx G t L S z K1 K2 g) :
    S ⊔ zpowers g ≤ hatCent t z := by
  obtain ⟨hgz, -, e3⟩ := sec10A2_conj_tz hb hctx
  refine sup_le (fun s hs => ?_) (Subgroup.zpowers_le.mpr ?_)
  · have hst : s * t = t * s := Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 hs)
    refine sec10D_mem_hatCent (Subgroup.mem_centralizer_singleton_iff.mpr (hctx.central s hs))
      (Or.inl ?_)
    calc s * t * s⁻¹ = (t * s) * s⁻¹ := by rw [hst]
      _ = t := by group
  · exact sec10D_mem_hatCent (Subgroup.mem_centralizer_singleton_iff.mpr hgz) (Or.inr e3)

theorem sec10A2_conj_K0 (h : Asc82Res10a) (hb : Asc82Basic10)
    (hctx : Sec10A2Ctx G t L S z K1 K2 g) :
    ∀ y ∈ S ⊔ zpowers g, ∀ x ∈ secK0 t z, y * x * y⁻¹ ∈ secK0 t z := by
  obtain ⟨ht2, hz2, ht1, -, hne, htz⟩ := sec10D_basic hb hctx.toSec10Ctx
  intro y hy x hx
  exact sec10D_hatCent_normalizes_K0 h.lK0 hctx.toSec10Ctx ht2 hz2 htz ht1 hne
    (sec10A2_T_le_hatCent hb hctx hy) x hx

theorem sec10A2_conj_oddCoreIn {X : Subgroup G} {c : G} (hc : ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (hc' : ∀ x ∈ X, c⁻¹ * x * c ∈ X) {y : G} (hy : y ∈ oddCoreIn X) :
    c * y * c⁻¹ ∈ oddCoreIn X := by
  set P : Subgroup G := (oddCoreIn X).map (MulAut.conj c).toMonoidHom with hP
  have hPX : P ≤ X := by
    rintro _ ⟨u, hu, rfl⟩
    exact hc u (CFSG.ClassicalInvolution.Balance.oddCoreIn_le X hu)
  have hPodd : Odd (Nat.card P) := by
    rw [hP, Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn X
  have hPn : ∀ h ∈ X, ∀ s ∈ P, h * s * h⁻¹ ∈ P := by
    intro h hh s hs
    obtain ⟨u, hu, rfl⟩ := hs
    refine ⟨(c⁻¹ * h * c) * u * (c⁻¹ * h * c)⁻¹,
      CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn (hc' h hh) hu, ?_⟩
    show c * ((c⁻¹ * h * c) * u * (c⁻¹ * h * c)⁻¹) * c⁻¹ = h * (c * u * c⁻¹) * h⁻¹
    group
  have hnorm : X ≤ normalizer (P : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨fun hs => hPn h hh s hs, fun hs => ?_⟩
    have := hPn h⁻¹ (X.inv_mem hh) _ hs
    simpa [mul_assoc] using this
  have hle : P ≤ oddCoreIn X :=
    CFSG.ClassicalInvolution.Balance.le_oddCoreIn_of_normalizes hPX hnorm hPodd
  exact hle ⟨y, hy, rfl⟩

theorem sec10A2_conj_N0 (h : Asc82Res10a) (hb : Asc82Basic10)
    (hctx : Sec10A2Ctx G t L S z K1 K2 g) :
    ∀ y ∈ S ⊔ zpowers g, ∀ x ∈ oddCoreIn (secK0 t z), y * x * y⁻¹ ∈ oddCoreIn (secK0 t z) := by
  intro y hy x hx
  refine sec10A2_conj_oddCoreIn (sec10A2_conj_K0 h hb hctx y hy) (fun w hw => ?_) hx
  have := sec10A2_conj_K0 h hb hctx y⁻¹ ((S ⊔ zpowers g).inv_mem hy) w hw
  simpa using this

theorem sec10A2_split (h3 : Asc82Sec3Res10) (h : Asc82Res10a) (hf : Asc82Facts10)
    (hb : Asc82Basic10) (hctx : Sec10Ctx G t L S z K1 K2) :
    IsDirectSplit (oddCoreIn (secK0 t z)) (K1 ⊔ K2) (secK0 t z) := by
  have hpsp : IsPSp43 L := (hb G t L S z hctx.toSec10Z).1
  have hLC : L ⊓ centralizer (L : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_psp43 hctx.component.isQuasisimple hpsp
  have hOC := sec10L104_oddK0_le_centralizer h.lK0 h3.l36 hf.pockets5 hf.centZ5 hb hctx
  have hKL : K1 ⊔ K2 ≤ L :=
    sup_le (hctx.pocket1.2.1.trans inf_le_left) (hctx.pocket2.2.1.trans inf_le_left)
  obtain ⟨hK1, hK2, -⟩ := sec10D_K0_contains h.lK0 hctx
  refine ⟨CFSG.ClassicalInvolution.Balance.oddCoreIn_le _, sup_le hK1 hK2, ?_, ?_,
    sec10L104_decomp h.lK0 h3.l36 hb hctx⟩
  · intro n hn k hk
    exact (Subgroup.mem_centralizer_iff.mp (hOC hn) k (hKL hk)).symm
  · intro x hxN hxK
    have hx : x ∈ L ⊓ centralizer (L : Set G) := ⟨hKL hxK, hOC hxN⟩
    rw [hLC] at hx
    simpa using hx

theorem sec10A2_exists_act (h3 : Asc82Sec3Res10) (h : Asc82Res10a) (hf : Asc82Facts10)
    (hb : Asc82Basic10) (hctx : Sec10A2Ctx G t L S z K1 K2 g) :
    ∃ f : ↥(S ⊔ zpowers g) →* MulAut ↥(K1 ⊔ K2),
      ∀ (y : ↥(S ⊔ zpowers g)) (k : ↥(K1 ⊔ K2)),
        ∃ n ∈ oddCoreIn (secK0 t z),
          (y : G) * (k : G) * (y : G)⁻¹ = n * ((f y k : ↥(K1 ⊔ K2)) : G) :=
  (sec10A2_split h3 h hf hb hctx.toSec10Ctx).exists_act (sec10A2_conj_K0 h hb hctx)
    (sec10A2_conj_N0 h hb hctx)

end CFSG.OddStandard.SmallF3.Omega
