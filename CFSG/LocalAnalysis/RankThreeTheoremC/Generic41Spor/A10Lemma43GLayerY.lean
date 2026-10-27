module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GDefs
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
public import CFSG.Foundations.Basic
public import CFSG.Open.GLADefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem a10t1_ly_mem_W {M : Subgroup G} {x w : G} :
    w ∈ M ⊓ Subgroup.centralizer ({x} : Set G) ↔ w ∈ M ∧ x * w = w * x := by
  simp [Subgroup.mem_centralizer_iff]

theorem a10t1_ly_f_data {M : Subgroup G} {x : G} (hxM : x ∈ M) (hx : x ^ 5 = 1) :
    ∃ f : ↥(M ⊓ Subgroup.centralizer ({x} : Set G)) →*
        ↥(Subgroup.centralizer ({a10π M ⟨x, hxM⟩} : Set (A10Y M))),
      Function.Surjective f ∧ ¬ 5 ∣ Nat.card f.ker ∧
      ∀ w : ↥(M ⊓ Subgroup.centralizer ({x} : Set G)),
        ((f w : ↥(Subgroup.centralizer ({a10π M ⟨x, hxM⟩} : Set (A10Y M)))) : A10Y M) =
          a10π M ⟨(w : G), (a10t1_ly_mem_W.mp w.2).1⟩ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hWM : M ⊓ Subgroup.centralizer ({x} : Set G) ≤ M := inf_le_left
  let g : ↥(M ⊓ Subgroup.centralizer ({x} : Set G)) →* A10Y M :=
    (a10π M).comp (Subgroup.inclusion hWM)
  have hmem : ∀ w, g w ∈ Subgroup.centralizer ({a10π M ⟨x, hxM⟩} : Set (A10Y M)) := by
    intro w
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    show a10π M ⟨x, hxM⟩ * a10π M (Subgroup.inclusion hWM w) =
      a10π M (Subgroup.inclusion hWM w) * a10π M ⟨x, hxM⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (a10t1_ly_mem_W.mp w.2).2
  refine ⟨g.codRestrict _ hmem, ?_, ?_, fun w => rfl⟩
  · have hy : ∃ n : ℕ, (⟨x, hxM⟩ : ↥M) ^ 5 ^ n = 1 :=
      ⟨1, Subtype.ext (by simpa using hx)⟩
    have hCD : (Subgroup.centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M)).map (a10π M) =
        Subgroup.centralizer ({a10π M ⟨x, hxM⟩} : Set (A10Y M)) :=
      CFSG.ComponentClassification.LBalance.Quot.map_centralizer_eq (p := 5) hy
    rintro ⟨d, hd⟩
    have hd' : d ∈ (Subgroup.centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M)).map (a10π M) := by
      rw [hCD]; exact hd
    obtain ⟨c, hc, hcd⟩ := Subgroup.mem_map.mp hd'
    refine ⟨⟨c.1, a10t1_ly_mem_W.mpr ⟨c.2, ?_⟩⟩, Subtype.ext ?_⟩
    · have := Subgroup.mem_centralizer_iff.mp hc ⟨x, hxM⟩ rfl
      exact congrArg Subtype.val this
    · exact hcd
  · rw [MonoidHom.ker_codRestrict]
    have hle : (g.ker).map (Subgroup.inclusion hWM) ≤ primeComplementCore (G := ↥M) 5 := by
      rintro _ ⟨k, hk, rfl⟩
      have : a10π M (Subgroup.inclusion hWM k) = 1 := hk
      exact (QuotientGroup.eq_one_iff _).mp this
    have hdvd : Nat.card (g.ker.map (Subgroup.inclusion hWM)) ∣
        Nat.card (primeComplementCore (G := ↥M) 5) := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hWM)] at hdvd
    intro h5
    have hcop : Nat.Coprime 5 (Nat.card g.ker) :=
      Nat.Coprime.coprime_dvd_right hdvd (primeComplementCore_coprime (G := ↥M) 5)
    exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mp hcop) h5

theorem a10t1_ly_img_map {M : Subgroup G} {x : G} (hxM : x ∈ M)
    (f : ↥(M ⊓ Subgroup.centralizer ({x} : Set G)) →*
        ↥(Subgroup.centralizer ({a10π M ⟨x, hxM⟩} : Set (A10Y M))))
    (hfv : ∀ w : ↥(M ⊓ Subgroup.centralizer ({x} : Set G)),
        ((f w : ↥(Subgroup.centralizer ({a10π M ⟨x, hxM⟩} : Set (A10Y M)))) : A10Y M) =
          a10π M ⟨(w : G), (a10t1_ly_mem_W.mp w.2).1⟩)
    (S : Subgroup ↥(M ⊓ Subgroup.centralizer ({x} : Set G))) :
    a10Img M (S.map (M ⊓ Subgroup.centralizer ({x} : Set G)).subtype) =
      (S.map f).map (Subgroup.centralizer ({a10π M ⟨x, hxM⟩} : Set (A10Y M))).subtype := by
  ext y
  simp only [a10Img, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨m, ⟨s, hs, hsm⟩, rfl⟩
    refine ⟨f s, ⟨s, hs, rfl⟩, ?_⟩
    rw [Subgroup.coe_subtype, hfv]
    congr 1
    exact Subtype.ext hsm
  · rintro ⟨d, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨⟨(s : G), (a10t1_ly_mem_W.mp s.2).1⟩, ⟨s, hs, rfl⟩, ?_⟩
    rw [Subgroup.coe_subtype, hfv]

theorem a10t1_ly_quot_congr {H : Type*} [Group H] {A B : Subgroup H} (h : A = B) :
    Nonempty (↥A ⧸ primeComplementCore (G := ↥A) 5 ≃* ↥B ⧸ primeComplementCore (G := ↥B) 5) := by
  subst h
  exact ⟨MulEquiv.refl _⟩

theorem a10t1_ly_quot_subgroupOf {H : Type*} [Group H] {A J : Subgroup H} (hJA : J ≤ A) :
    Nonempty (↥(J.subgroupOf A) ⧸ primeComplementCore (G := ↥(J.subgroupOf A)) 5 ≃*
      ↥J ⧸ primeComplementCore (G := ↥J) 5) :=
  ⟨QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJA)
    (CFSG.pPrimeCore_map_iso 5 (Subgroup.subgroupOfEquivOfLe hJA))⟩

theorem a10_layer_Y {M : Subgroup G} {x : G} {E₁ E₂ : Subgroup G} (hxM : x ∈ M) (hx : x ^ 5 = 1)
    (hc₁ : GLAPComponent 5 (M ⊓ Subgroup.centralizer ({x} : Set G)) E₁)
    (hc₂ : GLAPComponent 5 (M ⊓ Subgroup.centralizer ({x} : Set G)) E₂) (hne : E₁ ≠ E₂)
    (hlay : GLAPLayer 5 (M ⊓ Subgroup.centralizer ({x} : Set G)) = E₁ ⊔ E₂)
    (hA₁ : Nonempty (↥E₁ ⧸ primeComplementCore (G := ↥E₁) 5 ≃* alternatingGroup (Fin 5)))
    (hA₂ : Nonempty (↥E₂ ⧸ primeComplementCore (G := ↥E₂) 5 ≃* alternatingGroup (Fin 5))) :
    GLAPComponent 5 (Subgroup.centralizer ({a10π M ⟨x, hxM⟩} : Set (A10Y M))) (a10Img M E₁) ∧
      GLAPComponent 5 (Subgroup.centralizer ({a10π M ⟨x, hxM⟩} : Set (A10Y M))) (a10Img M E₂) ∧
      a10Img M E₁ ≠ a10Img M E₂ ∧
      GLAPLayer 5 (Subgroup.centralizer ({a10π M ⟨x, hxM⟩} : Set (A10Y M))) =
        a10Img M E₁ ⊔ a10Img M E₂ ∧
      Nonempty (↥(a10Img M E₁) ⧸ primeComplementCore (G := ↥(a10Img M E₁)) 5 ≃*
        alternatingGroup (Fin 5)) ∧
      Nonempty (↥(a10Img M E₂) ⧸ primeComplementCore (G := ↥(a10Img M E₂)) 5 ≃*
        alternatingGroup (Fin 5)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp5 : Nat.Prime 5 := by norm_num
  set W : Subgroup G := M ⊓ Subgroup.centralizer ({x} : Set G) with hW
  set D : Subgroup (A10Y M) :=
    Subgroup.centralizer ({a10π M ⟨x, hxM⟩} : Set (A10Y M)) with hD
  obtain ⟨f, hf, hker, hfv⟩ : ∃ f : ↥W →* ↥D, Function.Surjective f ∧ ¬ 5 ∣ Nat.card f.ker ∧
      ∀ w : ↥W, ((f w : ↥D) : A10Y M) = a10π M ⟨(w : G), (a10t1_ly_mem_W.mp w.2).1⟩ :=
    a10t1_ly_f_data hxM hx
  obtain ⟨hbij, -, hquot⟩ :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
      (p := 5) f hf hker
  have hWM : W ≤ M := inf_le_left
  have hcomp : ∀ E : Subgroup G, GLAPComponent 5 W E →
      E ≤ W ∧ CFSG.IsPComponent 5 (E.subgroupOf W) ∧ a10Img M E ≤ D ∧
        (a10Img M E).subgroupOf D = (E.subgroupOf W).map f ∧
        GLAPComponent 5 D (a10Img M E) := by
    intro E hE
    obtain ⟨hEW, hE'⟩ :=
      (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp5).mp hE
    have himg : a10Img M E = ((E.subgroupOf W).map f).map D.subtype := by
      have := a10t1_ly_img_map hxM f hfv (E.subgroupOf W)
      rwa [Subgroup.map_subgroupOf_eq_of_le hEW] at this
    have hle : a10Img M E ≤ D := by
      rw [himg]
      exact Subgroup.map_subtype_le _
    have hsub : (a10Img M E).subgroupOf D = (E.subgroupOf W).map f := by
      rw [himg]
      exact Subgroup.comap_map_eq_self_of_injective D.subtype_injective _
    refine ⟨hEW, hE', hle, hsub, ?_⟩
    rw [CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp5]
    exact ⟨hle, by rw [hsub]; exact hbij.mapsTo hE'⟩
  obtain ⟨hE₁W, hE₁', hle₁, hsub₁, hcE₁⟩ := hcomp E₁ hc₁
  obtain ⟨hE₂W, hE₂', hle₂, hsub₂, hcE₂⟩ := hcomp E₂ hc₂
  refine ⟨hcE₁, hcE₂, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 : (E₁.subgroupOf W).map f = (E₂.subgroupOf W).map f := by
      rw [← hsub₁, ← hsub₂, h]
    have h2 : E₁.subgroupOf W = E₂.subgroupOf W := hbij.injOn hE₁' hE₂' h1
    apply hne
    have := Subgroup.subgroupOf_inj.mp h2
    rwa [inf_eq_left.mpr hE₁W, inf_eq_left.mpr hE₂W] at this
  · have hl1 : CFSG.pLayer ↥D 5 = (CFSG.pLayer ↥W 5).map f := by
      have h1 := (Subgroup.gc_map_comap f).l_sSup_eq_sSup_image
        (s := {L : Subgroup ↥W | CFSG.IsPComponent 5 L})
      have h2 : (Subgroup.map f) '' {L : Subgroup ↥W | CFSG.IsPComponent 5 L} =
          {K : Subgroup ↥D | CFSG.IsPComponent 5 K} := hbij.image_eq
      unfold CFSG.pLayer
      rw [h1, h2]
    rw [CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPLayer_eq_map hp5 D, hl1,
      ← a10t1_ly_img_map hxM f hfv (CFSG.pLayer ↥W 5),
      ← CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPLayer_eq_map hp5 W, hlay]
    unfold a10Img
    rw [Subgroup.subgroupOf_sup (hE₁W.trans hWM) (hE₂W.trans hWM), Subgroup.map_sup]
  · obtain ⟨e₁⟩ := hA₁
    obtain ⟨e₂, -⟩ := hquot (E₁.subgroupOf W) hE₁'
    obtain ⟨e₃⟩ := a10t1_ly_quot_subgroupOf hE₁W
    obtain ⟨e₄⟩ := a10t1_ly_quot_congr hsub₁
    obtain ⟨e₅⟩ := a10t1_ly_quot_subgroupOf hle₁
    exact ⟨e₅.symm.trans (e₄.trans (e₂.symm.trans (e₃.trans e₁)))⟩
  · obtain ⟨e₁⟩ := hA₂
    obtain ⟨e₂, -⟩ := hquot (E₂.subgroupOf W) hE₂'
    obtain ⟨e₃⟩ := a10t1_ly_quot_subgroupOf hE₂W
    obtain ⟨e₄⟩ := a10t1_ly_quot_congr hsub₂
    obtain ⟨e₅⟩ := a10t1_ly_quot_subgroupOf hle₂
    exact ⟨e₅.symm.trans (e₄.trans (e₂.symm.trans (e₃.trans e₁)))⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
