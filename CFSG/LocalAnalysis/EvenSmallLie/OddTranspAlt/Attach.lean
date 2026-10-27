module

public import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.Local
public import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.PermComb

public section

namespace CFSG.EvenSmallLie.OddTranspAlt

open Equiv Equiv.Perm CFSG.Open

private theorem conj_comm_iff {M : Type*} [Group M] (h x y : M) :
    h * x * h⁻¹ * (h * y * h⁻¹) = h * y * h⁻¹ * (h * x * h⁻¹) ↔ x * y = y * x := by
  have e : ∀ u v : M, h * u * h⁻¹ * (h * v * h⁻¹) = h * (u * v) * h⁻¹ := fun u v => by group
  rw [e, e, mul_left_inj, mul_right_inj]

private theorem conj_inv_comm_iff {M : Type*} [Group M] (h x y : M) :
    h⁻¹ * x * h * (h⁻¹ * y * h) = h⁻¹ * y * h * (h⁻¹ * x * h) ↔ x * y = y * x := by
  have e : ∀ u v : M, h⁻¹ * u * h * (h⁻¹ * v * h) = h⁻¹ * (u * v) * h := fun u v => by group
  rw [e, e, mul_left_inj, mul_right_inj]

private theorem not_disjoint_self {n : ℕ} {σ : Perm (Fin n)} (hσ : σ.IsSwap) : ¬ σ.Disjoint σ :=
  fun hd => hσ.isCycle.ne_one (disjoint_refl_iff.1 hd)

namespace Cfg

variable {G : Type} [Group G] [Finite G] {n : ℕ} (c : Cfg G n)

omit [Finite G] in
private theorem mem_Dloc_conj {x d h : G} :
    x ∈ c.Dloc d ↔ h⁻¹ * x * h ∈ c.Dloc (h⁻¹ * d * h) := by
  have e := c.Dloc_conj_iff (x := x) (d := d) (h := h⁻¹)
  rwa [inv_inv] at e

private theorem mem_Dloc_iff_disjoint {x b : G} (hx : x ∈ c.Dt) (hb : b ∈ c.Dt) :
    x ∈ c.Dloc b ↔ (c.φ x).Disjoint (c.φ b) := by
  refine ⟨fun hxb => c.disjoint_of_comm hx hb hxb.2.1 hxb.2.2.symm, fun hd => ?_⟩
  refine ⟨hx.1, ?_, (c.comm_of_disjoint hx hb hd).symm⟩
  rintro rfl
  exact not_disjoint_self (c.φ_isSwap hx) hd

theorem exists_attach : ∃ a ∈ cls c.t, c.t * a ≠ a * c.t ∧ ∃ b ∈ c.Dt, b * a = a * b := by
  obtain ⟨g, hg⟩ := c.Dt_nonempty
  obtain ⟨h, hgh⟩ := exists_conj_of_mem_cls (c.Dt_subset_cls hg)
  have hgt : h⁻¹ * g * h = c.t := by rw [hgh]; group
  have ht'' : h⁻¹ * c.t * h ∈ c.Dt := by
    have e := (c.mem_Dloc_conj (h := h)).1 (show c.t ∈ c.Dloc g from
      ⟨c.t_mem_cls, fun e => hg.2.1 e.symm, hg.2.2.symm⟩)
    rwa [hgt] at e
  obtain ⟨f, hfs, hfne, hfnd⟩ := exists_swap_meeting (by have := c.hn; omega) (c.φ_isSwap ht'')
  obtain ⟨a'', ha'', rfl⟩ := c.exists_Dt_φ_eq hfs
  have hnc : h⁻¹ * c.t * h * a'' ≠ a'' * (h⁻¹ * c.t * h) := by
    rw [ne_eq, c.comm_iff_Dt ht'' ha'', isSwap_commute_iff (c.φ_isSwap ht'') hfs]
    rintro (e | hd)
    · exact hfne e.symm
    · exact hfnd hd.symm
  refine ⟨h * a'' * h⁻¹, conj_mem_cls ha''.1 h, ?_, g, hg, ?_⟩
  · rwa [ne_eq, ← conj_inv_comm_iff h, show h⁻¹ * (h * a'' * h⁻¹) * h = a'' by group]
  · rw [hgh]
    exact (conj_comm_iff h c.t a'').2 ha''.2.2

private def Nb (a b : G) : Set G := {x | x ∈ c.Dt ∧ x ∈ c.Dloc b ∧ x * a ≠ a * x}

theorem exists_star_pt {a : G} (ha : a ∈ cls c.t) (hta : c.t * a ≠ a * c.t) {b : G}
    (hb : b ∈ c.Dt) (hba : b * a = a * b) :
    ∃ ρ : Fin n, c.φ b ρ = ρ ∧
      ∀ x ∈ c.Dt, (c.φ x).Disjoint (c.φ b) → (x * a = a * x ↔ c.φ x ρ = ρ) := by
  obtain ⟨h, hbh⟩ := exists_conj_of_mem_cls (c.Dt_subset_cls hb)
  have hbt : h⁻¹ * b * h = c.t := by rw [hbh]; group
  have T1 : ∀ x, x ∈ c.Dloc b ↔ h⁻¹ * x * h ∈ c.Dt := fun x => by
    have e := c.mem_Dloc_conj (x := x) (d := b) (h := h)
    rwa [hbt] at e
  have T2 : ∀ x, x ∈ c.Dt ↔ h⁻¹ * x * h ∈ c.Dloc (h⁻¹ * c.t * h) := fun x =>
    c.mem_Dloc_conj (x := x) (d := c.t) (h := h)
  have ht'' : h⁻¹ * c.t * h ∈ c.Dt :=
    (T1 c.t).1 ⟨c.t_mem_cls, fun e => hb.2.1 e.symm, hb.2.2.symm⟩
  have ha'' : h⁻¹ * a * h ∈ c.Dt :=
    (T1 a).1 ⟨ha, fun e => hta (by rw [e]; exact hb.2.2), hba⟩
  have hnc'' : h⁻¹ * c.t * h * (h⁻¹ * a * h) ≠ h⁻¹ * a * h * (h⁻¹ * c.t * h) := by
    rwa [ne_eq, conj_inv_comm_iff]
  have hs₁ := c.φ_isSwap ht''
  have hs₂ := c.φ_isSwap ha''
  have hne₁₂ : c.φ (h⁻¹ * c.t * h) ≠ c.φ (h⁻¹ * a * h) := fun e =>
    hnc'' ((c.comm_iff_Dt ht'' ha'').2 (by rw [e]))
  have hnd₁₂ : ¬ (c.φ (h⁻¹ * c.t * h)).Disjoint (c.φ (h⁻¹ * a * h)) := fun hd =>
    hnc'' (c.comm_of_disjoint ht'' ha'' hd)
  have memF₃ : ∀ x ∈ c.Nb a b, h⁻¹ * x * h ∈ c.Dt ∧ (c.φ (h⁻¹ * x * h)).IsSwap ∧
      (c.φ (h⁻¹ * x * h)).Disjoint (c.φ (h⁻¹ * c.t * h)) ∧
      c.φ (h⁻¹ * x * h) * c.φ (h⁻¹ * a * h) ≠ c.φ (h⁻¹ * a * h) * c.φ (h⁻¹ * x * h) := by
    rintro x ⟨hxD, hxb, hxa⟩
    have hy := (T1 x).1 hxb
    refine ⟨hy, c.φ_isSwap hy, (c.mem_Dloc_iff_disjoint hy ht'').1 ((T2 x).1 hxD), ?_⟩
    rwa [ne_eq, ← c.comm_iff_Dt hy ha'', conj_inv_comm_iff]
  obtain ⟨S₃, hS₃, hS₃card⟩ : ∃ S : Finset (Perm (Fin n)), (∀ f, f ∈ S ↔ f.IsSwap ∧
      f.Disjoint (c.φ (h⁻¹ * c.t * h)) ∧ f * c.φ (h⁻¹ * a * h) ≠ c.φ (h⁻¹ * a * h) * f) ∧
      S.card = n - 3 :=
    ⟨_, fun f => by simp, card_noncomm hs₁ hs₂ hne₁₂ hnd₁₂⟩
  have hNb : (c.Nb a b).ncard = n - 3 := by
    rw [← hS₃card, ← Set.ncard_coe_finset]
    refine Set.ncard_congr (fun x _ => c.φ (h⁻¹ * x * h))
      (fun x hx => Finset.mem_coe.2 ((hS₃ _).2 (memF₃ x hx).2)) ?_ ?_
    · intro x x' hx hx' e
      have := c.φ_injOn (memF₃ x hx).1 (memF₃ x' hx').1 e
      exact (mul_right_inj h⁻¹).1 ((mul_left_inj h).1 this)
    · intro f hf
      obtain ⟨hfs, hfd, hfc⟩ := (hS₃ f).1 (Finset.mem_coe.1 hf)
      obtain ⟨y, hy, rfl⟩ := c.exists_Dt_φ_eq hfs
      have hyx : h⁻¹ * (h * y * h⁻¹) * h = y := by group
      refine ⟨h * y * h⁻¹, ⟨(T2 _).2 ?_, (T1 _).2 ?_, ?_⟩, congrArg c.φ hyx⟩
      · rw [hyx]; exact (c.mem_Dloc_iff_disjoint hy ht'').2 hfd
      · rw [hyx]; exact hy
      · rwa [ne_eq, ← conj_inv_comm_iff h, hyx, c.comm_iff_Dt hy ha'']
  have hinj : Set.InjOn c.φ (c.Nb a b) := c.φ_injOn.mono fun x hx => hx.1
  have hFcard : (c.φ '' c.Nb a b).ncard = n - 3 := by rw [hinj.ncard_image, hNb]
  have hFint : ∀ f ∈ c.φ '' c.Nb a b, ∀ g ∈ c.φ '' c.Nb a b, f ≠ g → ¬ f.Disjoint g := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne hd
    have hne' : c.φ (h⁻¹ * x * h) ≠ c.φ (h⁻¹ * y * h) := by
      intro e
      apply hne
      have := c.φ_injOn (memF₃ x hx).1 (memF₃ y hy).1 e
      rw [(mul_right_inj h⁻¹).1 ((mul_left_inj h).1 this)]
    apply noncomm_pairwise hs₁ hs₂ hne₁₂ hnd₁₂ (memF₃ x hx).2 (memF₃ y hy).2 hne'
    rw [← c.comm_iff_Dt (memF₃ x hx).1 (memF₃ y hy).1, conj_inv_comm_iff]
    exact c.comm_of_disjoint hx.1 hy.1 hd
  have hFfin : (c.φ '' c.Nb a b).Finite := Set.toFinite _
  obtain ⟨ρ, hρ⟩ := exists_common_point_of_pairwise_inter hFfin.toFinset
    (fun f hf => by
      obtain ⟨x, hx, rfl⟩ := hFfin.mem_toFinset.1 hf
      exact c.φ_isSwap hx.1)
    (by rw [← Set.ncard_eq_toFinset_card _ hFfin, hFcard]; have := c.hn; omega)
    (fun f hf g hg => hFint f (hFfin.mem_toFinset.1 hf) g (hFfin.mem_toFinset.1 hg))
  have hρ' : ∀ x ∈ c.Nb a b, c.φ x ρ ≠ ρ := fun x hx =>
    hρ _ (hFfin.mem_toFinset.2 ⟨x, hx, rfl⟩)
  have hbρ : c.φ b ρ = ρ := by
    obtain ⟨_, ⟨x, hx, rfl⟩⟩ := Set.nonempty_of_ncard_ne_zero (s := c.φ '' c.Nb a b)
      (by rw [hFcard]; have := c.hn; omega)
    exact ((c.mem_Dloc_iff_disjoint hx.1 hb).1 hx.2.1 ρ).resolve_left (hρ' x hx)
  obtain ⟨S, hS, hScard⟩ : ∃ S : Finset (Perm (Fin n)),
      (∀ f, f ∈ S ↔ f.IsSwap ∧ f.Disjoint (c.φ b) ∧ f ρ ≠ ρ) ∧ S.card = n - 3 :=
    ⟨_, fun f => by simp, card_star (c.φ_isSwap hb) hbρ⟩
  have hFS : c.φ '' c.Nb a b = ↑S := by
    refine Set.eq_of_subset_of_ncard_le ?_ (by rw [Set.ncard_coe_finset, hScard, hFcard])
      S.finite_toSet
    rintro _ ⟨x, hx, rfl⟩
    exact Finset.mem_coe.2 ((hS _).2 ⟨c.φ_isSwap hx.1,
      (c.mem_Dloc_iff_disjoint hx.1 hb).1 hx.2.1, hρ' x hx⟩)
  refine ⟨ρ, hbρ, fun x hx hd => ⟨fun hxa => ?_, fun hxρ => ?_⟩⟩
  · by_contra hxρ
    have hmem : c.φ x ∈ c.φ '' c.Nb a b := by
      rw [hFS]; exact Finset.mem_coe.2 ((hS _).2 ⟨c.φ_isSwap hx, hd, hxρ⟩)
    obtain ⟨y, hy, e⟩ := hmem
    exact hy.2.2 (by rw [c.φ_injOn hy.1 hx e]; exact hxa)
  · by_contra hxa
    exact hρ' x ⟨hx, (c.mem_Dloc_iff_disjoint hx hb).2 hd, hxa⟩ hxρ

theorem exists_star {a : G} (ha : a ∈ cls c.t) (hta : c.t * a ≠ a * c.t)
    (hex : ∃ b ∈ c.Dt, b * a = a * b) :
    ∃ ρ : Fin n, ∀ x ∈ c.Dt, (x * a = a * x ↔ c.φ x ρ = ρ) := by
  have hmem : ∀ x ∈ c.Dt,
      c.φ x ∈ c.φ '' {y | y ∈ c.Dt ∧ y * a = a * y} ↔ x * a = a * x := by
    intro x hx
    refine ⟨?_, fun hxa => ⟨x, ⟨hx, hxa⟩, rfl⟩⟩
    rintro ⟨y, ⟨hy, hya⟩, e⟩
    rwa [← c.φ_injOn hy hx e]
  obtain ⟨ρ, hρ⟩ := star_lemma c.hn (c.φ '' {y | y ∈ c.Dt ∧ y * a = a * y})
    (by rintro _ ⟨y, ⟨hy, -⟩, rfl⟩; exact c.φ_isSwap hy)
    (by obtain ⟨b, hb, hba⟩ := hex; exact ⟨c.φ b, b, ⟨hb, hba⟩, rfl⟩)
    (by
      rintro _ ⟨b, ⟨hb, hba⟩, rfl⟩
      obtain ⟨ρ, hbρ, hρ⟩ := c.exists_star_pt ha hta hb hba
      refine ⟨ρ, hbρ, fun f hf hd => ?_⟩
      obtain ⟨x, hx, rfl⟩ := c.exists_Dt_φ_eq hf
      rw [hmem x hx]
      exact hρ x hx hd)
  exact ⟨ρ, fun x hx => (hmem x hx).symm.trans (hρ _ (c.φ_isSwap hx))⟩

structure Attachment where
  a : G
  ρ : Fin n
  mem : a ∈ cls c.t
  ne : c.t * a ≠ a * c.t
  star : ∀ x ∈ c.Dt, (x * a = a * x ↔ c.φ x ρ = ρ)
  ord_x : ∀ x ∈ c.Dt, x * a ≠ a * x → orderOf (x * a) = 3
  ord_t : orderOf (a * c.t) = 3

theorem nonempty_attachment : Nonempty c.Attachment := by
  obtain ⟨a, ha, hta, b, hb, hba⟩ := c.exists_attach
  obtain ⟨ρ, hρ⟩ := c.exists_star ha hta ⟨b, hb, hba⟩
  refine ⟨⟨a, ρ, ha, hta, hρ, fun x hx hxa => ?_, ?_⟩⟩
  ·
    have hxρ : c.φ x ρ ≠ ρ := fun e => hxa ((hρ x hx).2 e)
    obtain ⟨f, hfs, hfd, hfρ⟩ :=
      exists_swap_disjoint_fixing (by have := c.hn; omega) (c.φ_isSwap hx) ρ
    obtain ⟨y, hy, rfl⟩ := c.exists_Dt_φ_eq hfs
    have hxy : x ≠ y := by rintro rfl; exact hxρ hfρ
    have hay : a ≠ y := by rintro rfl; exact hta hy.2.2
    exact c.orderOf_mul_Dloc_three hy.1 ⟨hx.1, hxy, c.comm_of_disjoint hy hx hfd⟩
      ⟨ha, hay, (hρ y hy).2 hfρ⟩ hxa
  · have hab : a ≠ b := by rintro rfl; exact hta hb.2.2
    exact c.orderOf_mul_Dloc_three hb.1 ⟨ha, hab, hba⟩
      ⟨c.t_mem_cls, Ne.symm hb.2.1, hb.2.2.symm⟩ (Ne.symm hta)

end Cfg

end CFSG.EvenSmallLie.OddTranspAlt
