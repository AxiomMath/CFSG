module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122Mod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122Sec
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122Yc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121T

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S E : Subgroup G}

private theorem normalizer_commutator_aux {Y1 Y2 : Subgroup G} {g : G}
    (h1 : g ∈ normalizer (Y1 : Set G)) (h2 : g ∈ normalizer (Y2 : Set G)) :
    g ∈ normalizer ((⁅Y1, Y2⁆ : Subgroup G) : Set G) := by
  have key : ∀ {g : G}, g ∈ normalizer (Y1 : Set G) → g ∈ normalizer (Y2 : Set G) →
      ∀ x ∈ ⁅Y1, Y2⁆, g * x * g⁻¹ ∈ ⁅Y1, Y2⁆ := by
    intro g hg1 hg2 x hx
    have hmap : (⁅Y1, Y2⁆).map (MulAut.conj g).toMonoidHom ≤ ⁅Y1, Y2⁆ := by
      rw [Subgroup.map_commutator]
      refine Subgroup.commutator_mono ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hg1 y).mp hy
      · rintro _ ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hg2 y).mp hy
    simpa [MulAut.conj_apply] using hmap (Subgroup.mem_map_of_mem _ hx)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key h1 h2 x, fun hx => ?_⟩
  have hinv1 : g⁻¹ ∈ normalizer (Y1 : Set G) := (normalizer (Y1 : Set G)).inv_mem h1
  have hinv2 : g⁻¹ ∈ normalizer (Y2 : Set G) := (normalizer (Y2 : Set G)).inv_mem h2
  have h := key hinv1 hinv2 _ hx
  have h' : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
  rwa [h'] at h

theorem sec122_Yc_le_normalizer_V (F : Sec12Frame t L S)
    (hSc : S ≤ centralizer ({t} : Set G)) (hSE : S ≤ normalizer (E : Set G))
    (hMLE : secM t S L ⊓ L ≤ normalizer (E : Set G)) :
    (secM t S L ⊓ L) ⊔ S ≤ normalizer (secV t S L E : Set G) := by
  intro g hg
  have hgE : g ∈ normalizer (E : Set G) := sup_le hMLE hSE hg
  have hgY : g ∈ normalizer ((secM t S L ⊓ L : Subgroup G) : Set G) :=
    sec122_Yc_le_normalizer_Y F hSc hg
  exact normalizer_commutator_aux hgE hgY

theorem sec122_mod_exists (F : Sec12Frame t L S) (hE : IsSylow2Of E (secCMB t S L))
    (hVab : IsElemAb2 (secV t S L E) 8) {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L)
      (alternatingGroup (Fin 5))) :
    ∃ (s : (Fin 5 → ZMod 2) → G) (W : Subgroup G),
      Sec122Mod t (secV t S L E) (secB S L) (secM t S L ⊓ L) W φ s := by
  have hcommSub : ∀ a b : ↥(secV t S L E), a * b = b * a :=
    isMulCommutative_iff.mp hVab.1.1
  have hcomm : ∀ v ∈ secV t S L E, ∀ w ∈ secV t S L E, v * w = w * v := by
    intro v hv w hw
    exact congrArg Subtype.val (hcommSub ⟨v, hv⟩ ⟨w, hw⟩)
  have hsq : ∀ v ∈ secV t S L E, v * v = 1 := by
    intro v hv
    have h := hVab.1.2 v hv
    rwa [pow_two] at h
  have htriv : ∀ y ∈ secM t S L ⊓ L,
      (∀ v, IsEvenVec v → y * φ v * y⁻¹ = φ v) →
      ∀ x ∈ secV t S L E, y * x * y⁻¹ = x := by
    intro y hy hfix x hx
    have hyCent : y ∈ centralizer (secB S L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨v, hv, hv_eq⟩ := (hperm.2.2.1 b).mp hb
      subst hv_eq
      have h' : y * φ v = φ v * y := by
        calc y * φ v = (y * φ v * y⁻¹) * y := by group
          _ = φ v * y := by rw [hfix v hv]
      exact h'.symm
    have hyB : y ∈ secB S L := by
      have hmem : y ∈ centralizer (secB S L : Set G) ⊓ L := ⟨hyCent, hy.2⟩
      rwa [F.bdata.2.2.1] at hmem
    have hyV : y ∈ secV t S L E := sec121_B_le_V F hE hyB
    calc y * x * y⁻¹ = x * y * y⁻¹ := by rw [hcomm y hyV x hx]
      _ = x := by group
  have hVP : secV t S L E ≤ secCMB t S L := (sec121_V_le_E F hE).trans hE.1
  have hfB : ∀ v ∈ secV t S L E, sec12f t v ∈ secB S L :=
    fun v hv => sec12E_f_mem F (hVP hv)
  have hfmul : ∀ v ∈ secV t S L E, ∀ w ∈ secV t S L E,
      sec12f t (v * w) = sec12f t v * sec12f t w :=
    fun v hv w hw => sec12E_f_mul F (hVP hv) (hVP hw)
  have hfconj : ∀ y ∈ secM t S L ⊓ L, ∀ v ∈ secV t S L E,
      sec12f t (y * v * y⁻¹) = y * sec12f t v * y⁻¹ := by
    intro y hy v hv
    have hyt : y * t = t * y := (Subgroup.mem_centralizer_iff.mp F.htC) y hy.2
    exact sec12E_f_conj hyt v
  obtain ⟨s, hsV, hsadd, hsf, hsY⟩ :=
    sec122_section hcomm hsq hperm
      (fun y hy v hv =>
        (Subgroup.mem_normalizer_iff.mp (sec121_Y_le_normalizer_V F hE hy) v).mp hv)
      htriv hfB hfmul hfconj (fun b hb => sec121_f_surj_V F hE hb)
  obtain ⟨W, hW⟩ := sec122_exists_W hsadd
  refine ⟨s, W, ?_⟩
  exact {
    comm := hcomm
    sq := hsq
    BV := sec121_B_le_V F hE
    perm := hperm
    fB := hfB
    fmul := hfmul
    fker := fun v hv => sec121_f_eq_one_iff_V F hE hv
    sV := hsV
    sadd := hsadd
    sf := hsf
    sY := hsY
    hW := hW }

end CFSG.OddStandard.SmallF3.Omega
