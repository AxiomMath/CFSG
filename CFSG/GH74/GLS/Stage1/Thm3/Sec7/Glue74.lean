module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue74b
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Core74
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue74a

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t u : G} {q : ℕ}

namespace Cfg7

theorem ctx74 (hII : II4_4_4_center) (hg : IG_10_32_P) (h : Cfg7 G z S K₁ K₂ t u q)
    (hc73 : Concl73 z S K₁ K₂) {E₂ : Subgroup G} (hE₂E : E₂ ≤ S ⊓ centralizer ({t} : Set G))
    (hE₂idx : ∀ e ∈ S ⊓ centralizer ({t} : Set G), ∀ e' ∈ S ⊓ centralizer ({t} : Set G),
      e ∈ E₂ ∨ e' ∈ E₂ ∨ e⁻¹ * e' ∈ E₂) (hzE₂ : z ∉ E₂) (htE₂ : t ∈ E₂) :
    C74.Ctx74 z t S (Pof S K₁) (Pof S K₂) (S1 S K₁) (S ⊓ centralizer ({t} : Set G)) E₂ where
  z_sq := h.z_sq
  z_ne := h.z_ne
  zP₁ := h.z_mem_P hII (Or.inl rfl)
  zP₂ := h.z_mem_P hII (Or.inr rfl)
  P₁S₁ := h.P₁_le_S1
  P₂S₁ := h.P₂_le_S1 hII
  S₁S := S1_le_S
  P₁P₂ := h.P_comm hII
  P₁₂ := (h.P_inf hII).le
  S₁P₁ := h.S1_normalizes_P₁
  zS := fun s hs => Subgroup.mem_centralizer_singleton_iff.1 (h.S_le_C hII hs)
  t_mem := h.ch.t_mem
  t_sq := h.t_sq
  t_nS₁ := h.t_nS1
  S₁idx := h.S1_relIndex
  tP₁ := h.tP₁
  tP₂ := h.tP₂
  hE := fun x => by rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  frat := h.frat hII hg hc73
  E₂E := hE₂E
  E₂idx := hE₂idx
  zE₂ := hzE₂
  tE₂ := htE₂

theorem data74 (hII : II4_4_4_center) (hq : II4_4_quat) (hqm : Quat_mod_center) (h41 : Prop4_1)
    (hg : IG_10_32_P) (h : Cfg7 G z S K₁ K₂ t u q) (hc73 : Concl73 z S K₁ K₂) :
    ∃ D : Subgroup G, Data74 z S K₁ K₂ t D := by
  obtain ⟨E₂, hE₂E, hE₂idx, hzE₂, htE₂⟩ := h.exists_E₂ hII h41
  have c := h.ctx74 hII hg hc73 hE₂E hE₂idx hzE₂ htE₂
  obtain ⟨hDS, hprod, hquot, hidx, hinter⟩ := C74.core74 c
  obtain ⟨hNq, ⟨e⟩⟩ := hquot
  obtain ⟨hNz, ⟨e2⟩⟩ := hinter
  refine ⟨C74.Dsub (S ⊓ centralizer ({t} : Set G)) (S1 S K₁) E₂, hDS, hprod, ⟨hNq, ⟨e⟩⟩, ?_, ?_, ?_⟩
  · obtain ⟨hN, hds⟩ := h.std.p66.2.2.1 K₂ (by simp)
    have hQP : Qof S K₂ = Pof S K₁ := hc73.2.2
    rcases hds with ⟨n, hn⟩ | ⟨n, hn⟩
    · left; exact ⟨n, dih_transport e (dih_of_eq hQP hn)⟩
    · right; exact ⟨n, sd_transport e (sd_of_eq hQP hn)⟩
  · obtain ⟨n, hn⟩ := hq G h.std.std.simple z h.std.std.orderOf_z S K₂ h.std.std.sylow
      (h.std.std.comp_isPCompIn (Or.inr rfl)) (h.std.std.comp_pRank (Or.inr rfl))
    obtain ⟨hN, hdih⟩ := hqm G (Pof S K₂) z n hn (h.z_mem_P hII (Or.inr rfl)) h.std.std.orderOf_z
    rw [h.Pz_eq_sup hII]
    exact ⟨2 ^ (n - 1), dihOrder_transport e2.symm hdih⟩
  · rw [h.Pz_eq_sup hII]; exact hidx

theorem cls_Y0 (hII : II4_4_4_center) (hg : IG_10_32_P) (h : Cfg7 G z S K₁ K₂ t u q) :
    ∀ y ∈ (Pof S K₁ ⊔ Pof S K₂) ⊔ zpowers t, orderOf y = 2 → IsConj z y ∨ IsConj (t * z) y := by
  intro y hy hyo
  rcases h.Y0_elems hII hy with hP | ⟨p, hp, hpe⟩
  · by_cases hyz : y = z
    · left; exact isConj_iff.2 ⟨1, by simp [hyz]⟩
    · right
      exact h.ch.t_fus y (by rw [h.Pz_eq_sup hII]; exact hP) hyo hyz
  · obtain ⟨c, hcP, hc⟩ := hg G z S K₁ K₂ h.std.std t h.ch.t_mem h.t_ord h.ch.t_swap y
      (by rw [hpe, h.Pz_eq_sup hII]; simpa using hp) hyo
    rcases hc with h1 | h2
    · left; exact h.ch.t_conj.trans (isConj_iff.2 ⟨c, h1⟩)
    · right; exact isConj_iff.2 ⟨c, h2⟩

theorem inv_classes_S (hII : II4_4_4_center) (hg : IG_10_32_P) (h : Cfg7 G z S K₁ K₂ t u q)
    (hc73 : Concl73 z S K₁ K₂) :
    ∀ x ∈ S, orderOf x = 2 → IsConj z x ∨ IsConj (t * z) x := by
  intro x hxS hx
  by_cases hxY : x ∈ (Pof S K₁ ⊔ Pof S K₂) ⊔ zpowers t
  · exact h.cls_Y0 hII hg x hxY hx
  · have hle := h.Y0_relIndex hII hc73
    have hpos := C73.relIndex_pos ((Pof S K₁ ⊔ Pof S K₂) ⊔ zpowers t) S
    have hne : ((Pof S K₁ ⊔ Pof S K₂) ⊔ zpowers t).relIndex S ≠ 1 := fun h1 =>
      hxY (Subgroup.relIndex_eq_one.1 h1 hxS)
    have hidx : ((Pof S K₁ ⊔ Pof S K₂) ⊔ zpowers t).relIndex S = 2 := by omega
    obtain ⟨g, hgY, -⟩ := h.transfer hII ((Pof S K₁ ⊔ Pof S K₂) ⊔ zpowers t) x (h.Y0_le hII) hidx
      hxS hxY (mul_self_eq_one_of_orderOf_eq_two hx)
    have hord : orderOf (g⁻¹ * x * g) = 2 := by
      have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective x
      simpa [MulAut.conj_apply, hx] using this
    have hconj : IsConj (g⁻¹ * x * g) x := isConj_iff.2 ⟨g, by group⟩
    rcases h.cls_Y0 hII hg _ hgY hord with k | k
    · left; exact k.trans hconj
    · right; exact k.trans hconj

theorem inv_classes (hII : II4_4_4_center) (hg : IG_10_32_P) (h : Cfg7 G z S K₁ K₂ t u q)
    (hc73 : Concl73 z S K₁ K₂) : ∀ x : G, orderOf x = 2 → IsConj z x ∨ IsConj (t * z) x := by
  intro x hx
  have hM := h.m4 hII
  have hx2 : x * x = 1 := mul_self_eq_one_of_orderOf_eq_two hx
  have hx1 : x ≠ 1 := ne_one_of_orderOf_eq_two hx
  obtain ⟨P', hP', hxP'⟩ := M.exists_syl2In_ge (M.isPGroup_zpowers_of_sq hx2 hx1)
    (le_top : zpowers x ≤ ⊤)
  obtain ⟨cc, -, hcc⟩ := hM.S_top.exists_conj hP'
  have hx' : cc * x * cc⁻¹ ∈ S := by
    have : x ∈ P' := hxP' (mem_zpowers x)
    rw [hcc, M.mem_cj] at this
    exact this
  have hord : orderOf (cc * x * cc⁻¹) = 2 := by
    have := orderOf_injective (MulAut.conj cc).toMonoidHom (MulAut.conj cc).injective x
    simpa [MulAut.conj_apply, hx] using this
  have hconj : IsConj x (cc * x * cc⁻¹) := isConj_iff.2 ⟨cc, rfl⟩
  rcases h.inv_classes_S hII hg hc73 _ hx' hord with k | k
  · left; exact k.trans hconj.symm
  · right; exact k.trans hconj.symm

theorem half_central (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) :
    IsHalfTwoCentral (t * z) := by
  have hM := h.m4 hII
  obtain ⟨cc, hcc⟩ := isConj_iff.1 (h.ch.t_fus u h.ch.u_mem h.ch.u_ord h.ch.u_ne)
  have hSsyl : M.Syl2In S ⊤ := hM.S_top
  have hT : M.Syl2In (M.cj S cc) (M.cj ⊤ cc) := M.syl2In_cj hSsyl cc
  have hcjtop : M.cj (⊤ : Subgroup G) cc = ⊤ := by ext x; simp
  rw [hcjtop] at hT
  let Tsyl : Sylow 2 G := hT.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hT.2.2)
  have hTcoe : (Tsyl : Subgroup G) = M.cj S cc := IsPGroup.toSylow_coe _ _
  have huS : u ∈ S := h.ch.u_mem.1
  have htz : cc⁻¹ * u * cc = t * z := by rw [← hcc]; group
  refine ⟨Tsyl, ?_, ?_⟩
  · rw [hTcoe, M.mem_cj, hcc]; exact huS
  · rw [hTcoe]
    have hcent : centralizer ({t * z} : Set G) = M.cj (centralizer ({u} : Set G)) cc := by
      rw [M.cj_centralizer, htz]
    have e : M.cj S cc ⊓ centralizer ({t * z} : Set G) =
        M.cj (S ⊓ centralizer ({u} : Set G)) cc := by
      rw [hcent, M.cj_inf]
    rw [e, relIndex_cj]
    apply A.relIndex_le_two_of_pigeon
    intro s hs s' hs'
    have hfix : ∀ x ∈ S, x * u * x⁻¹ = u → x ∈ S ⊓ centralizer ({u} : Set G) := by
      intro x hx hxu
      refine Subgroup.mem_inf.2 ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      calc x * u = (x * u * x⁻¹) * x := by group
        _ = u * x := by rw [hxu]
    by_cases h1 : s * u * s⁻¹ = u
    · exact Or.inl (hfix s hs h1)
    by_cases h2 : s' * u * s'⁻¹ = u
    · exact Or.inr (Or.inl (hfix s' hs' h2))
    right; right
    have hs1 : s * u * s⁻¹ = u * z := (h.ch.u_norm s hs).resolve_left h1
    have hs2 : s' * u * s'⁻¹ = u * z := (h.ch.u_norm s' hs').resolve_left h2
    refine Subgroup.mem_inf.2 ⟨S.mul_mem (S.inv_mem hs) hs',
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc s⁻¹ * s' * u = s⁻¹ * (s' * u * s'⁻¹) * s' := by group
      _ = s⁻¹ * (s * u * s⁻¹) * s' := by rw [hs1, hs2]
      _ = u * (s⁻¹ * s') := by group

theorem concl74c (hII : II4_4_4_center) (hg : IG_10_32_P) (h : Cfg7 G z S K₁ K₂ t u q)
    (hc73 : Concl73 z S K₁ K₂) : Concl74c z t :=
  ⟨h.inv_classes hII hg hc73, h.ch.tz_ne, h.half_central hII⟩

end Cfg7

theorem lemma_7_4 (hII : II4_4_4_center) (hq : II4_4_quat) (hqm : Quat_mod_center) (h41 : Prop4_1)
    (hg : IG_10_32_P) : Lemma7_4 := by
  intro G _ _ z S K₁ K₂ t u q h hc73
  exact ⟨h.data74 hII hq hqm h41 hg hc73, h.concl74c hII hg hc73⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec7
