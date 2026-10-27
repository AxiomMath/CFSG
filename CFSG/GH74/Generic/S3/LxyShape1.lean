module

public import CFSG.GH74.Generic.S3.LyTrans
public import CFSG.GH74.GLS.TwoThin.G.Reduction

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.GLS.TwoThin CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.GLS (InG2 InC2 InT2 InB2 InCalK2 HasSL2Model)
open CFSG.GH74.Filter.ClassicalOdd (Q8)
open scoped MatrixGroups commutatorElement

section YX

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

theorem NbrData.lxy_sq (hnd : NbrData G t p f x y Iw Iv) : (y * x) * (y * x) = 1 := by
  have hy := hnd.y_sq
  have hx := hnd.x_sq
  calc y * x * (y * x) = y * (x * y) * x := by group
    _ = y * (y * x) * x := by rw [← hnd.comm]
    _ = (y * y) * (x * x) := by group
    _ = 1 := by rw [hy, hx, one_mul]

theorem NbrData.lxy_ne_one (hnd : NbrData G t p f x y Iw Iv) : y * x ≠ 1 := by
  intro h
  apply hnd.ne
  have hx := hnd.x_sq
  calc y = y * (x * x) := by rw [hx, mul_one]
    _ = (y * x) * x := by rw [mul_assoc]
    _ = x := by rw [h, one_mul]

theorem NbrData.lxy_inv (hnd : NbrData G t p f x y Iw Iv) : orderOf (y * x) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact hnd.lxy_sq) hnd.lxy_ne_one

theorem NbrData.lxy_x_mem (hnd : NbrData G t p f x y Iw Iv) :
    x ∈ centralizer ({y * x} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * (y * x) = (x * y) * x := by rw [mul_assoc]
    _ = (y * x) * x := by rw [← hnd.comm]

theorem NbrData.lxy_y_mem (hnd : NbrData G t p f x y Iw Iv) :
    y ∈ centralizer ({y * x} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc y * (y * x) = y * (x * y) := by rw [hnd.comm]
    _ = (y * x) * y := by rw [← mul_assoc]

theorem NbrData.lxy_Iv_le (hnd : NbrData G t p f x y Iw Iv) :
    Iv ≤ centralizer ({y * x} : Set G) := by
  intro i hi
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hix : i * x = x * i := Subgroup.mem_centralizer_singleton_iff.1 (hnd.comp_w.1.1 (hnd.Iv_le hi))
  have hiy : i * y = y * i := hnd.Iv_central i hi
  calc i * (y * x) = (i * y) * x := by rw [mul_assoc]
    _ = (y * i) * x := by rw [hiy]
    _ = y * (i * x) := by rw [mul_assoc]
    _ = y * (x * i) := by rw [hix]
    _ = (y * x) * i := by rw [mul_assoc]

theorem NbrData.lxy_isPCompIn (hnd : NbrData G t p f x y Iw Iv) :
    CFSG.GH74.GLS.IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({y * x} : Set G)) Iv := by
  have heq : centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) =
      centralizer ({x} : Set G) ⊓ centralizer ({y * x} : Set G) := by
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hgx, hgy⟩
      refine ⟨hgx, ?_⟩
      calc g * (y * x) = (g * y) * x := by rw [mul_assoc]
        _ = (y * g) * x := by rw [hgy]
        _ = y * (g * x) := by rw [mul_assoc]
        _ = y * (x * g) := by rw [hgx]
        _ = (y * x) * g := by rw [mul_assoc]
    · rintro ⟨hgx, hgyx⟩
      refine ⟨hgx, ?_⟩
      have hx := hnd.x_sq
      have hyeq : y = (y * x) * x := by
        calc y = y * (x * x) := by rw [hx, mul_one]
          _ = (y * x) * x := by rw [mul_assoc]
      calc g * y = g * ((y * x) * x) := by rw [← hyeq]
        _ = (g * (y * x)) * x := by rw [← mul_assoc]
        _ = ((y * x) * g) * x := by rw [hgyx]
        _ = (y * x) * (g * x) := by rw [mul_assoc]
        _ = (y * x) * (x * g) := by rw [hgx]
        _ = ((y * x) * x) * g := by rw [← mul_assoc]
        _ = y * g := by rw [← hyeq]
  have := hnd.isPCompIn_Iv
  rwa [heq] at this

end YX

section BarAt

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

theorem NbrData.lxy_proj_injective (hnd : NbrData G t p f x y Iw Iv) {v : G}
    (hIv : Iv ≤ centralizer ({v} : Set G)) :
    Function.Injective ((proj v).comp (Subgroup.inclusion hIv) : ↥Iv →* CentralizerBar v) := by
  set φ₀ : ↥Iv →* CentralizerBar v := (proj v).comp (Subgroup.inclusion hIv) with hφ₀
  rw [← MonoidHom.ker_eq_bot_iff]
  obtain ⟨F, hFf, hFfin, hF, ⟨e⟩⟩ := hnd.Iv_iso
  have h5 := hnd.prime.2.2
  have hy1 : φ₀ ⟨y, hnd.y_Iv⟩ ≠ 1 := by
    intro h1
    exact hnd.y_ne_one (S45.eq_one_of_proj_eq_one_of_sq (hIv hnd.y_Iv) h1 hnd.y_sq)
  have hycen : (⟨y, hnd.y_Iv⟩ : ↥Iv) ∈ Subgroup.center ↥Iv := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hnd.Iv_central g g.2)
  rcases CFSG.ClassicalInvolution.normal_cases_of_equiv_sl2 (by rw [hF]; omega) e.symm φ₀.ker
      (MonoidHom.normal_ker φ₀) with h | h | h
  · exact h
  · exact absurd (h ▸ hycen) (fun hy => hy1 (MonoidHom.mem_ker.1 hy))
  · exact absurd (show (⟨y, hnd.y_Iv⟩ : ↥Iv) ∈ φ₀.ker by rw [h]; trivial) (fun hy => hy1 hy)

theorem NbrData.lxy_barSub_equiv (hnd : NbrData G t p f x y Iw Iv) {v : G}
    (hIv : Iv ≤ centralizer ({v} : Set G)) :
    ∃ φ : ↥Iv ≃* ↥(S45.barSub v Iv),
      ∀ w : ↥Iv, ((φ w : ↥(S45.barSub v Iv)) : CentralizerBar v) = proj v ⟨(w : G), hIv w.2⟩ := by
  set φ₀ : ↥Iv →* CentralizerBar v := (proj v).comp (Subgroup.inclusion hIv) with hφ₀
  have hrange : φ₀.range = S45.barSub v Iv := by
    ext c
    constructor
    · rintro ⟨j, rfl⟩
      exact S45.proj_mem_barSub (hIv j.2) j.2
    · intro hc
      obtain ⟨g, hg, hgJ, rfl⟩ := S45.mem_barSub.1 hc
      exact ⟨⟨g, hgJ⟩, rfl⟩
  exact ⟨(MonoidHom.ofInjective (hnd.lxy_proj_injective hIv)).trans (MulEquiv.subgroupCongr hrange),
    fun w => rfl⟩

theorem NbrData.lxy_barSub_isQuasisimple (hnd : NbrData G t p f x y Iw Iv) {v : G}
    (hIv : Iv ≤ centralizer ({v} : Set G)) : IsQuasisimple ↥(S45.barSub v Iv) := by
  obtain ⟨φ, -⟩ := hnd.lxy_barSub_equiv hIv
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv φ hnd.Iv_quasisimple

end BarAt

section YXBar

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

@[expose] noncomputable def NbrData.lxyY (hnd : NbrData G t p f x y Iw Iv) : CentralizerBar (y * x) :=
  proj (y * x) ⟨y, hnd.lxy_y_mem⟩

@[expose] noncomputable def NbrData.lxyS (hnd : NbrData G t p f x y Iw Iv) :
    barQ ↥(centralizer ({y * x} : Set G)) :=
  barMk ↥(centralizer ({y * x} : Set G)) ⟨x, hnd.lxy_x_mem⟩

theorem NbrData.lxyY_mem (hnd : NbrData G t p f x y Iw Iv) : hnd.lxyY ∈ S45.barSub (y * x) Iv :=
  S45.proj_mem_barSub hnd.lxy_y_mem hnd.y_Iv

theorem NbrData.lxyY_sq (hnd : NbrData G t p f x y Iw Iv) : hnd.lxyY * hnd.lxyY = 1 := by
  unfold NbrData.lxyY
  rw [← map_mul]
  have : (⟨y, hnd.lxy_y_mem⟩ : ↥(centralizer ({y * x} : Set G))) * ⟨y, hnd.lxy_y_mem⟩ = 1 :=
    Subtype.ext hnd.y_sq
  rw [this, map_one]

theorem NbrData.lxyY_ne_one (hnd : NbrData G t p f x y Iw Iv) : hnd.lxyY ≠ 1 := fun h =>
  hnd.y_ne_one (S45.eq_one_of_proj_eq_one_of_sq hnd.lxy_y_mem h hnd.y_sq)

theorem NbrData.lxyY_central (hnd : NbrData G t p f x y Iw Iv) :
    ∀ l ∈ S45.barSub (y * x) Iv, l * hnd.lxyY = hnd.lxyY * l := by
  intro l hl
  obtain ⟨g, hg, hgJ, rfl⟩ := S45.mem_barSub.1 hl
  unfold NbrData.lxyY
  rw [← map_mul, ← map_mul]
  have : (⟨g, hg⟩ : ↥(centralizer ({y * x} : Set G))) * ⟨y, hnd.lxy_y_mem⟩ =
      ⟨y, hnd.lxy_y_mem⟩ * ⟨g, hg⟩ := Subtype.ext (hnd.Iv_central g hgJ)
  rw [this]

theorem NbrData.lxy_center_ne_bot (hnd : NbrData G t p f x y Iw Iv) :
    Subgroup.center ↥(S45.barSub (y * x) Iv) ≠ ⊥ := by
  intro h
  have hz : (⟨hnd.lxyY, hnd.lxyY_mem⟩ : ↥(S45.barSub (y * x) Iv)) ∈
      Subgroup.center ↥(S45.barSub (y * x) Iv) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hnd.lxyY_central g g.2)
  rw [h, Subgroup.mem_bot] at hz
  exact hnd.lxyY_ne_one (congrArg Subtype.val hz)

theorem NbrData.lxy_barSub_inB2 (hnd : NbrData G t p f x y Iw Iv) :
    GLS.InB2 ↥(S45.barSub (y * x) Iv) := by
  obtain ⟨φ, -⟩ := hnd.lxy_barSub_equiv hnd.lxy_Iv_le
  obtain ⟨F, hFf, hFfin, hF, ⟨e⟩⟩ := hnd.Iv_iso
  have hoddF : Odd (Nat.card F) := by
    rw [hF]; exact (hnd.prime.1.odd_of_ne_two hnd.prime.2.1).pow
  refine ⟨⟨hnd.lxy_barSub_isQuasisimple hnd.lxy_Iv_le,
    Or.inr (Or.inl ⟨F, hFf, hFfin, hoddF, ⟨?_⟩⟩)⟩, hnd.lxy_center_ne_bot⟩
  exact (φ.symm.trans e.symm).trans (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 2 F).symm

theorem NbrData.lxyS_eq (hnd : NbrData G t p f x y Iw Iv) :
    hnd.lxyS = xbar (y * x) * hnd.lxyY := by
  unfold NbrData.lxyS NbrData.lxyY xbar
  have hxe : (⟨x, hnd.lxy_x_mem⟩ : ↥(centralizer ({y * x} : Set G))) =
      ⟨y * x, Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh; rw [hh]⟩ * ⟨y, hnd.lxy_y_mem⟩ := by
    apply Subtype.ext
    change x = (y * x) * y
    calc x = (y * y) * x := by rw [hnd.y_sq, one_mul]
      _ = y * (y * x) := by rw [mul_assoc]
      _ = y * (x * y) := by rw [hnd.comm]
      _ = (y * x) * y := by rw [mul_assoc]
  rw [hxe, map_mul]
  rfl

theorem NbrData.lxyS_conj (hnd : NbrData G t p f x y Iw Iv) (l : CentralizerBar (y * x)) :
    hnd.lxyS * l * hnd.lxyS⁻¹ = hnd.lxyY * l * hnd.lxyY⁻¹ := by
  rw [hnd.lxyS_eq]
  have hc := Subgroup.mem_center_iff.1 (xbar_mem_center (y * x))
  have hinv : (xbar (y * x))⁻¹ ∈ Subgroup.center (CentralizerBar (y * x)) :=
    Subgroup.inv_mem _ (xbar_mem_center (y * x))
  have hc' := Subgroup.mem_center_iff.1 hinv
  calc xbar (y * x) * hnd.lxyY * l * (xbar (y * x) * hnd.lxyY)⁻¹
      = xbar (y * x) * (hnd.lxyY * l * hnd.lxyY⁻¹) * (xbar (y * x))⁻¹ := by group
    _ = (hnd.lxyY * l * hnd.lxyY⁻¹) * xbar (y * x) * (xbar (y * x))⁻¹ := by
        rw [hc (hnd.lxyY * l * hnd.lxyY⁻¹)]
    _ = hnd.lxyY * l * hnd.lxyY⁻¹ := by group

end YXBar

section YXPump

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

theorem NbrData.lxyS_orderOf (hnd : NbrData G t p f x y Iw Iv) : orderOf hnd.lxyS = 2 :=
  orderOf_barMk (orderOf_mk_centralizer hnd.lxy_x_mem hnd.x_inv)

theorem NbrData.lxy_isPCompIn_bar (hnd : NbrData G t p f x y Iw Iv) :
    CFSG.GH74.GLS.IsPCompIn 2
      (centralizer ({hnd.lxyS} : Set (barQ ↥(centralizer ({y * x} : Set G)))))
      (S45.barSub (y * x) Iv) := by
  have hso := orderOf_mk_centralizer hnd.lxy_x_mem hnd.x_inv
  have hB := hnd.lxy_isPCompIn
  have hΛC := le_centralizer_mk hB.1 hnd.lxy_x_mem
  have hΛ := isTwoComponent_centralizer_mk hB hnd.lxy_x_mem
  have hIC : S45.barSub (y * x) Iv ≤
      centralizer ({hnd.lxyS} : Set (barQ ↥(centralizer ({y * x} : Set G)))) :=
    (Subgroup.map_mono hΛC).trans (map_centralizer_barMk hso).le
  exact isPCompIn_two_iff.mpr ⟨hIC, isTwoComponent_map_barMk hso hΛC hΛ⟩

theorem NbrData.lxy_conjSub_eq (hnd : NbrData G t p f x y Iw Iv)
    {L : Subgroup (barQ ↥(centralizer ({y * x} : Set G)))} (hle : S45.barSub (y * x) Iv ≤ L) :
    conjSub hnd.lxyS⁻¹ L = L := by
  ext l
  rw [mem_conjSub_iff', inv_inv, hnd.lxyS_conj]
  have hy : hnd.lxyY ∈ L := hle hnd.lxyY_mem
  constructor
  · intro h
    have h2 : hnd.lxyY⁻¹ * (hnd.lxyY * l * hnd.lxyY⁻¹) * hnd.lxyY ∈ L :=
      L.mul_mem (L.mul_mem (L.inv_mem hy) h) hy
    simpa [mul_assoc] using h2
  · intro h
    exact L.mul_mem (L.mul_mem hy h) (L.inv_mem hy)

theorem NbrData.lxy_vertical_inB2 (hKG : TwoThinKGroupVerticalQ Gen4Cen) (hgen : Gen4 G)
    (hnd : NbrData G t p f x y Iw Iv)
    {L : Subgroup (barQ ↥(centralizer ({y * x} : Set G)))} (hC2T2 : InC2 ↥L ∨ InT2 ↥L)
    (hL : CFSG.IsComponent L) (hle : S45.barSub (y * x) Iv ≤ L) : InB2 ↥L := by
  refine hKG (barQ ↥(centralizer ({y * x} : Set G))) (gen4Cen_barQ hgen hnd.lxy_inv)
    hnd.lxyS L (S45.barSub (y * x) Iv) ↥(S45.barSub (y * x) Iv) hnd.lxyS_orderOf hL hC2T2
    (hnd.lxy_conjSub_eq hle) hnd.lxy_isPCompIn_bar hle hnd.lxy_barSub_inB2
    ⟨MonoidHom.id _, Function.surjective_id, ?_⟩
  rw [MonoidHom.ker_id]
  simp

end YXPump

end CFSG.GH74.Generic.S3
