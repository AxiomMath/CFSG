module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndCfg
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltY
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltStab

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp
open scoped commutatorElement

section Stab

private def altIHstab (n : ℕ) (c d : Fin n) : Subgroup (alternatingGroup (Fin n)) where
  carrier := {σ | ∀ x : Fin n, (σ : Equiv.Perm (Fin n)) x ∈ ({c, d} : Finset (Fin n)) ↔
    x ∈ ({c, d} : Finset (Fin n))}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := by
    intro σ τ hσ hτ x
    exact (hσ _).trans (hτ x)
  inv_mem' := by
    intro σ hσ x
    have h := hσ (((σ : Equiv.Perm (Fin n))⁻¹) x)
    have h2 : (σ : Equiv.Perm (Fin n)) (((σ : Equiv.Perm (Fin n))⁻¹) x) = x :=
      Equiv.apply_symm_apply _ _
    rw [h2] at h
    exact h.symm

private theorem altIHstab_ge {n : ℕ} (c d : Fin n) : altStabilizer n {c, d} ≤ altIHstab n c d := by
  intro σ hσ x
  rw [mem_altStabilizer_iff] at hσ
  have hc := hσ c (by simp)
  have hd := hσ d (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact Or.inl ((σ : Equiv.Perm (Fin n)).injective (h.trans hc.symm))
    · exact Or.inr ((σ : Equiv.Perm (Fin n)).injective (h.trans hd.symm))
  · rintro (h | h)
    · exact Or.inl (by rw [h]; exact hc)
    · exact Or.inr (by rw [h]; exact hd)

private theorem altIHstab_conj {n : ℕ} {c d : Fin n} {g k : alternatingGroup (Fin n)}
    (hg : g ∈ altIHstab n c d) (hk : k ∈ altStabilizer n {c, d}) :
    g * k * g⁻¹ ∈ altStabilizer n {c, d} := by
  rw [mem_altStabilizer_iff] at hk ⊢
  intro i hi
  have h1 : (g⁻¹ : alternatingGroup (Fin n)) ∈ altIHstab n c d := inv_mem hg
  have h2 : ((g⁻¹ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) i ∈
      ({c, d} : Finset (Fin n)) := (h1 i).mpr hi
  have h3 := hk _ h2
  show (g : Equiv.Perm (Fin n)) ((k : Equiv.Perm (Fin n))
    (((g⁻¹ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) i)) = i
  rw [h3]
  exact Equiv.apply_symm_apply _ _

private theorem altIH_sq_aux {α : Type*} (g : Equiv.Perm α) {x y : α} (hxy : x ≠ y)
    (hx : g x = x ∨ g x = y) (hy : g y = x ∨ g y = y) : g (g x) = x := by
  rcases hx with h | h
  · rw [h, h]
  · rw [h]
    rcases hy with h' | h'
    · exact h'
    · exact absurd (g.injective (h'.trans h.symm)).symm hxy

private theorem altIHstab_sq {n : ℕ} {c d : Fin n} (hcd : c ≠ d) {g : alternatingGroup (Fin n)}
    (hg : g ∈ altIHstab n c d) : g * g ∈ altStabilizer n {c, d} := by
  rw [mem_altStabilizer_iff]
  have hgc : (g : Equiv.Perm (Fin n)) c ∈ ({c, d} : Finset (Fin n)) := (hg c).mpr (by simp)
  have hgd : (g : Equiv.Perm (Fin n)) d ∈ ({c, d} : Finset (Fin n)) := (hg d).mpr (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hgc hgd
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  show (g : Equiv.Perm (Fin n)) ((g : Equiv.Perm (Fin n)) i) = i
  rcases hi with hi | hi
  · rw [hi]
    exact altIH_sq_aux _ hcd hgc hgd
  · rw [hi]
    exact altIH_sq_aux _ hcd.symm hgd.symm hgc.symm

private theorem altIHstab_ne_top {n : ℕ} (hn : 4 ≤ n) (c d : Fin n) : altIHstab n c d ≠ ⊤ := by
  intro htop
  obtain ⟨e, -, he⟩ : ∃ e, e ∈ (Finset.univ : Finset (Fin n)) ∧
      e ∉ ({c, d} : Finset (Fin n)) := by
    apply Finset.exists_mem_notMem_of_card_lt_card
    have := Finset.card_le_two (a := c) (b := d)
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨f, -, hf⟩ : ∃ f, f ∈ (Finset.univ : Finset (Fin n)) ∧
      f ∉ ({c, d, e} : Finset (Fin n)) := by
    apply Finset.exists_mem_notMem_of_card_lt_card
    have := Finset.card_le_three (a := c) (b := d) (c := e)
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he hf
  have hsign : Equiv.swap c e * Equiv.swap e f ∈ alternatingGroup (Fin n) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (Ne.symm he.1),
      Equiv.Perm.sign_swap (Ne.symm hf.2.2)]
    rfl
  have hmem : (⟨Equiv.swap c e * Equiv.swap e f, hsign⟩ : alternatingGroup (Fin n)) ∈
      altIHstab n c d := htop ▸ Subgroup.mem_top _
  have h1 : (Equiv.swap c e * Equiv.swap e f) c ∈ ({c, d} : Finset (Fin n)) :=
    (hmem c).mpr (by simp)
  have h2 : (Equiv.swap c e * Equiv.swap e f) c = e := by
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm he.1) (Ne.symm hf.1),
      Equiv.swap_apply_left]
  rw [h2] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  grind

end Stab

section Invol

variable {n : ℕ} {a b c d : Fin n}

private theorem altIH_sign (hab : a ≠ b) (hcd : c ≠ d) :
    Equiv.swap a b * Equiv.swap c d ∈ alternatingGroup (Fin n) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hcd]
  rfl

private def altIHt (hab : a ≠ b) (hcd : c ≠ d) : alternatingGroup (Fin n) :=
  ⟨Equiv.swap a b * Equiv.swap c d, altIH_sign hab hcd⟩

private theorem altIHt_coe (hab : a ≠ b) (hcd : c ≠ d) :
    (altIHt hab hcd : Equiv.Perm (Fin n)) = Equiv.swap a b * Equiv.swap c d := rfl

private theorem altIHt_mem (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : altIHt hab hcd ∈ altIHstab n c d := by
  intro x
  simp only [altIHt_coe, Equiv.Perm.mul_apply, Finset.mem_insert, Finset.mem_singleton,
    Equiv.swap_apply_def]
  grind

private theorem altIHt_mul_self (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) : altIHt hab hcd * altIHt hab hcd = 1 := by
  have hnd : [a, b, c, d].Nodup := by simp [hab, hac, had, hbc, hbd, hcd]
  have hc : Commute (Equiv.swap a b) (Equiv.swap c d) :=
    (Equiv.Perm.disjoint_swap_swap hnd).commute
  apply Subtype.ext
  show (Equiv.swap a b * Equiv.swap c d) * (Equiv.swap a b * Equiv.swap c d) = 1
  rw [← pow_two, hc.mul_pow]
  simp [pow_two]

private theorem altIHt_ne_one (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) :
    altIHt hab hcd ≠ 1 := by
  intro h
  have h1 : (Equiv.swap a b * Equiv.swap c d) a = a := by
    have := congrArg Subtype.val h
    exact DFunLike.congr_fun this a
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hac had, Equiv.swap_apply_left] at h1
  exact hab h1.symm

private theorem altIH_comm_swap {σ : Equiv.Perm (Fin n)} (ha : σ a = a) (hb : σ b = b) :
    σ * Equiv.swap a b = Equiv.swap a b * σ := by
  have h := Equiv.swap_apply_apply σ a b
  rw [ha, hb] at h
  calc σ * Equiv.swap a b = (σ * Equiv.swap a b * σ⁻¹) * σ := by group
    _ = Equiv.swap a b * σ := by rw [← h]

private theorem altIHt_comm (hab : a ≠ b) (hcd : c ≠ d) {σ : alternatingGroup (Fin n)}
    (hσ : σ ∈ altStabilizer n {a, b, c, d}) : σ * altIHt hab hcd = altIHt hab hcd * σ := by
  rw [mem_altStabilizer_iff] at hσ
  have ha := hσ a (by simp)
  have hb := hσ b (by simp)
  have hc := hσ c (by simp)
  have hd := hσ d (by simp)
  apply Subtype.ext
  show (σ : Equiv.Perm (Fin n)) * (Equiv.swap a b * Equiv.swap c d) =
    (Equiv.swap a b * Equiv.swap c d) * (σ : Equiv.Perm (Fin n))
  rw [← mul_assoc, altIH_comm_swap ha hb, mul_assoc, altIH_comm_swap hc hd, mul_assoc]

end Invol

section Transport

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {n : ℕ}

private def altIHK (θ : ↥L ≃* alternatingGroup (Fin n)) (c d : Fin n) : Subgroup (MulAut V) :=
  ((altStabilizer n {c, d}).comap θ.toMonoidHom).map L.subtype

private def altIHG (θ : ↥L ≃* alternatingGroup (Fin n)) (c d : Fin n) : Subgroup (MulAut V) :=
  ((altIHstab n c d).comap θ.toMonoidHom).map L.subtype

variable {θ : ↥L ≃* alternatingGroup (Fin n)} {c d : Fin n}

private theorem mem_altIHK {x : MulAut V} :
    x ∈ altIHK θ c d ↔ ∃ hx : x ∈ L, θ ⟨x, hx⟩ ∈ altStabilizer n {c, d} := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l.2, hl⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

private theorem mem_altIHG {x : MulAut V} :
    x ∈ altIHG θ c d ↔ ∃ hx : x ∈ L, θ ⟨x, hx⟩ ∈ altIHstab n c d := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l.2, hl⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

private theorem altIHK_le_altIHG : altIHK θ c d ≤ altIHG θ c d :=
  Subgroup.map_mono (Subgroup.comap_mono (altIHstab_ge c d))

private theorem altIHK_le : altIHK θ c d ≤ L := Subgroup.map_subtype_le _

private theorem altIHG_le : altIHG θ c d ≤ L := Subgroup.map_subtype_le _

private theorem altIHK_map :
    ((altIHK θ c d).subgroupOf L).map θ.toMonoidHom = altStabilizer n {c, d} := by
  have h1 : (altIHK θ c d).subgroupOf L = (altStabilizer n {c, d}).comap θ.toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  rw [h1, Subgroup.map_comap_eq_self_of_surjective θ.surjective]

private theorem altIHG_ne (hn : 4 ≤ n) : altIHG θ c d ≠ L := by
  intro h
  obtain ⟨σ, hσ⟩ : ∃ σ : alternatingGroup (Fin n), σ ∉ altIHstab n c d := by
    by_contra hcon
    exact altIHstab_ne_top hn c d
      ((Subgroup.eq_top_iff' _).mpr fun σ => not_not.mp fun hσ => hcon ⟨σ, hσ⟩)
  have hx : ((θ.symm σ : ↥L) : MulAut V) ∈ altIHG θ c d := by
    rw [h]
    exact (θ.symm σ).2
  obtain ⟨hxL, hx'⟩ := mem_altIHG.mp hx
  have : θ ⟨((θ.symm σ : ↥L) : MulAut V), hxL⟩ = σ := θ.apply_symm_apply σ
  rw [this] at hx'
  exact hσ hx'

private theorem altIH_conj {g k : MulAut V} (hg : g ∈ altIHG θ c d) (hk : k ∈ altIHK θ c d) :
    g * k * g⁻¹ ∈ altIHK θ c d := by
  obtain ⟨hgL, hg'⟩ := mem_altIHG.mp hg
  obtain ⟨hkL, hk'⟩ := mem_altIHK.mp hk
  refine mem_altIHK.mpr ⟨L.mul_mem (L.mul_mem hgL hkL) (L.inv_mem hgL), ?_⟩
  have key : θ (⟨g, hgL⟩ * ⟨k, hkL⟩ * ⟨g, hgL⟩⁻¹) ∈ altStabilizer n {c, d} := by
    rw [map_mul, map_mul, map_inv]
    exact altIHstab_conj hg' hk'
  exact key

private theorem altIH_sq (hcd : c ≠ d) {g : MulAut V} (hg : g ∈ altIHG θ c d) :
    g * g ∈ altIHK θ c d := by
  obtain ⟨hgL, hg'⟩ := mem_altIHG.mp hg
  refine mem_altIHK.mpr ⟨L.mul_mem hgL hgL, ?_⟩
  have key : θ (⟨g, hgL⟩ * ⟨g, hgL⟩) ∈ altStabilizer n {c, d} := by
    rw [map_mul]
    exact altIHstab_sq hcd hg'
  exact key

private theorem altIH_Y_le {Y : Subgroup (MulAut V)} (hYL : Y ≤ L) {a b : Fin n}
    (hstab : (Y.subgroupOf L).map θ.toMonoidHom = altStabilizer n {a, b, c, d}) :
    Y ≤ altIHK θ c d := by
  intro y hy
  refine mem_altIHK.mpr ⟨hYL hy, ?_⟩
  have h1 : θ ⟨y, hYL hy⟩ ∈ altStabilizer n {a, b, c, d} := by
    rw [← hstab]
    exact ⟨⟨y, hYL hy⟩, hy, rfl⟩
  rw [mem_altStabilizer_iff] at h1 ⊢
  intro i hi
  apply h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi ⊢
  tauto

private def altIHtL (θ : ↥L ≃* alternatingGroup (Fin n)) {a b c d : Fin n} (hab : a ≠ b)
    (hcd : c ≠ d) : ↥L := θ.symm (altIHt hab hcd)

private theorem altIHtL_apply {a b : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    θ (altIHtL θ hab hcd) = altIHt hab hcd := θ.apply_symm_apply _

private theorem altIHtL_mem {a b : Fin n} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) : ((altIHtL θ hab hcd : ↥L) : MulAut V) ∈ altIHG θ c d := by
  refine mem_altIHG.mpr ⟨(altIHtL θ hab hcd).2, ?_⟩
  have : θ ⟨((altIHtL θ hab hcd : ↥L) : MulAut V), (altIHtL θ hab hcd).2⟩ = altIHt hab hcd :=
    altIHtL_apply hab hcd
  rw [this]
  exact altIHt_mem hab hcd hac had hbc hbd

private theorem altIHtL_sq {a b : Fin n} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    ((altIHtL θ hab hcd : ↥L) : MulAut V) ^ 2 = 1 := by
  have h1 : altIHtL θ hab hcd * altIHtL θ hab hcd = 1 := by
    apply θ.injective
    rw [map_mul, map_one, altIHtL_apply]
    exact altIHt_mul_self hab hcd hac had hbc hbd
  have h2 := congrArg Subtype.val h1
  rw [pow_two]
  exact h2

private theorem altIHtL_ne_one {a b : Fin n} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c)
    (had : a ≠ d) : ((altIHtL θ hab hcd : ↥L) : MulAut V) ≠ 1 := by
  intro h1
  have h2 : altIHtL θ hab hcd = 1 := Subtype.ext h1
  have h3 := congrArg θ h2
  rw [altIHtL_apply, map_one] at h3
  exact altIHt_ne_one hab hcd hac had h3

private theorem altIHtL_cent {Y : Subgroup (MulAut V)} (hYL : Y ≤ L) {a b : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hstab : (Y.subgroupOf L).map θ.toMonoidHom = altStabilizer n {a, b, c, d}) :
    ((altIHtL θ hab hcd : ↥L) : MulAut V) ∈ Subgroup.centralizer (Y : Set (MulAut V)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : θ ⟨y, hYL hy⟩ ∈ altStabilizer n {a, b, c, d} := by
    rw [← hstab]
    exact ⟨⟨y, hYL hy⟩, hy, rfl⟩
  have h2 := altIHt_comm hab hcd h1
  have h3 : (⟨y, hYL hy⟩ : ↥L) * altIHtL θ hab hcd = altIHtL θ hab hcd * ⟨y, hYL hy⟩ := by
    apply θ.injective
    rw [map_mul, map_mul, altIHtL_apply]
    exact h2
  exact congrArg Subtype.val h3

private theorem altIHK_equiv (hcd : c ≠ d) :
    Nonempty (↥(altIHK θ c d) ≃* alternatingGroup (Fin (n - 2))) := by
  have hmap : ((altStabilizer n {c, d}).comap θ.toMonoidHom).map θ.toMonoidHom =
      altStabilizer n {c, d} := Subgroup.map_comap_eq_self_of_surjective θ.surjective _
  have e : ↥(altIHK θ c d) ≃* alternatingGroup (Fin (n - ({c, d} : Finset (Fin n)).card)) :=
    (Subgroup.equivMapOfInjective ((altStabilizer n {c, d}).comap θ.toMonoidHom) L.subtype
      L.subtype_injective).symm.trans
      ((MulEquiv.subgroupMap θ ((altStabilizer n {c, d}).comap θ.toMonoidHom)).trans
        ((MulEquiv.subgroupCongr hmap).trans (altStabilizerEquiv {c, d})))
  rw [Finset.card_pair hcd] at e
  exact ⟨e⟩

private theorem altIHK_simple (hcd : c ≠ d) (hn : 7 ≤ n) : IsSimpleGroup ↥(altIHK θ c d) := by
  obtain ⟨e⟩ := altIHK_equiv (θ := θ) hcd
  have : IsSimpleGroup (alternatingGroup (Fin (n - 2))) :=
    alternatingGroup.isSimpleGroup (by simp; omega)
  exact e.isSimpleGroup

private theorem altIHK_perfect (hcd : c ≠ d) (hn : 7 ≤ n) :
    ⁅altIHK θ c d, altIHK θ c d⁆ = altIHK θ c d := by
  obtain ⟨e⟩ := altIHK_equiv (θ := θ) hcd
  have : Group.IsPerfect (alternatingGroup (Fin (n - 2))) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp; omega))
  have : Group.IsPerfect ↥(altIHK θ c d) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Subgroup.isPerfect_iff.mp inferInstance

private theorem altIHK_card (hcd : c ≠ d) (hn : 7 ≤ n) :
    Nat.card ↥(altIHK θ c d) = (n - 2).factorial / 2 := by
  obtain ⟨e⟩ := altIHK_equiv (θ := θ) hcd
  have : Nontrivial (Fin (n - 2)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]

end Transport

private theorem altIH_isKGroup {V : Type} [CommGroup V] {G K : Subgroup (MulAut V)}
    (hG : CFSG.IsKGroup ↥G) (hKG : K ≤ G) : CFSG.IsKGroup ↥K :=
  isKGroup_of_surjective (isKGroup_subgroup hG (K.subgroupOf G))
    (Subgroup.subgroupOfEquivOfLe hKG).toMonoidHom (Subgroup.subgroupOfEquivOfLe hKG).surjective

theorem EndCfg4.natSection_stab_two {V : Type} [CommGroup V] [Finite V]
    {G T Y : Subgroup (MulAut V)} (h : EndCfg4 G T Y) (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ}
    (hm : 7 ≤ m) (hodd : Odd m) (hY : YAlt Y m) {L : Subgroup (MulAut V)} (hLG : L ≤ G)
    (θ : ↥L ≃* alternatingGroup (Fin (m + 4))) (hYL : Y ≤ L) {a b c d : Fin (m + 4)}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hstab : (Y.subgroupOf L).map θ.toMonoidHom = altStabilizer (m + 4) {a, b, c, d}) :
    ∃ (K : Subgroup (MulAut V)) (θK : ↥K ≃* alternatingGroup (Fin (m + 2))),
      K ≤ L ∧ (K.subgroupOf L).map θ.toMonoidHom = altStabilizer (m + 4) {c, d} ∧
      IsNatSectionWith (altAct (m + 2)) θK (commV K) ⊥ := by
  classical
  obtain ⟨ε⟩ := hY
  have hn4 : 4 ≤ m + 4 := by omega
  have hn7 : 7 ≤ m + 4 := by omega
  have hYG : Y ≤ G := hYL.trans hLG
  have hYK : Y ≤ altIHK θ c d := altIH_Y_le hYL hstab
  have hKGs : altIHK θ c d ≤ altIHG θ c d := altIHK_le_altIHG
  have hGsL : altIHG θ c d ≤ L := altIHG_le
  have hGsG : altIHG θ c d ≤ G := hGsL.trans hLG
  have hYGs : Y ≤ altIHG θ c d := hYK.trans hKGs
  have htGs : ((altIHtL θ hab hcd : ↥L) : MulAut V) ∈ altIHG θ c d :=
    altIHtL_mem hab hcd hac had hbc hbd
  have htG : ((altIHtL θ hab hcd : ↥L) : MulAut V) ∈ G := hGsG htGs
  have htsq : ((altIHtL θ hab hcd : ↥L) : MulAut V) ^ 2 = 1 :=
    altIHtL_sq hab hcd hac had hbc hbd
  have ht1 : ((altIHtL θ hab hcd : ↥L) : MulAut V) ≠ 1 := altIHtL_ne_one hab hcd hac had
  have htY : ((altIHtL θ hab hcd : ↥L) : MulAut V) ∈ Subgroup.centralizer (Y : Set (MulAut V)) :=
    altIHtL_cent hYL hab hcd hstab
  generalize ((altIHtL θ hab hcd : ↥L) : MulAut V) = t at htGs htG htsq ht1 htY
  have hTcent : Subgroup.centralizer ((Subgroup.zpowers t : Subgroup (MulAut V)) :
      Set (MulAut V)) = Subgroup.centralizer ({t} : Set (MulAut V)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hadmG : Adm4 G (Subgroup.zpowers t) Y :=
    { hTG := Subgroup.zpowers_le.mpr htG
      hT1 := fun h0 => ht1 (Subgroup.zpowers_eq_bot.mp h0)
      hT2 := IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, orderOf_eq_prime htsq ht1, pow_one])
      hYC := le_inf hYG fun y hy => by
        rw [hTcent, Subgroup.mem_centralizer_iff]
        intro s hs
        rw [Set.mem_singleton_iff.mp hs]
        exact (Subgroup.mem_centralizer_iff.mp htY y hy).symm
      hsub := by
        rw [hTcent]
        exact h.cent t ⟨htG, htY⟩ ht1 htsq
      hperf := h.adm.hperf
      hcls := h.adm.hcls }
  have hadm : Adm4 (altIHG θ c d) (Subgroup.zpowers t) Y :=
    hadmG.restrict (Subgroup.zpowers_le.mpr htGs) hGsG hYGs
  have hlt : altIHG θ c d < L := lt_of_le_of_ne hGsL (altIHG_ne hn4)
  have hsmaller : Smaller (altIHG θ c d) G :=
    Or.inl (lt_of_lt_of_le (Subgroup.card_lt_of_lt hlt) (Subgroup.card_le_of_le hLG))
  obtain ⟨X, hYX, hXGs, hXsub, hcases⟩ :=
    h.ih V hV (altIHG θ c d) hsmaller (altIH_isKGroup h.kgroup hGsG) _ Y hadm
  have hYnt : Nontrivial ↥Y := by
    have : Nontrivial (alternatingGroup (Fin m)) :=
      alternatingGroup.nontrivial_of_three_le_card (by simp; omega)
    exact ε.toEquiv.nontrivial
  obtain ⟨y₀, hy₀⟩ : ∃ y : ↥Y, y ≠ 1 := exists_ne 1
  have hKX : altIHK θ c d ≤ X := by
    have hsub : (X.subgroupOf (altIHK θ c d)).IsSubnormal :=
      CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hKGs hXsub
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup (altIHK_simple hcd hn7) hsub with
      hbot | htop
    · exfalso
      have hmem : (⟨(y₀ : MulAut V), hYK y₀.2⟩ : ↥(altIHK θ c d)) ∈
          X.subgroupOf (altIHK θ c d) := hYX y₀.2
      rw [hbot, Subgroup.mem_bot] at hmem
      have h2 : (y₀ : MulAut V) = 1 := congrArg Subtype.val hmem
      exact hy₀ (Subtype.ext h2)
    · intro k hk
      have hmem : (⟨k, hk⟩ : ↥(altIHK θ c d)) ∈ X.subgroupOf (altIHK θ c d) := by
        rw [htop]
        trivial
      exact hmem
  have hcardK : Nat.card ↥(altIHK θ c d) = (m + 2).factorial / 2 := altIHK_card hcd hn7
  have hcardY : Nat.card ↥Y = m.factorial / 2 := by
    have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr ε.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  rcases hcases with ⟨hXcls, -⟩ | ⟨k, hk2, -, hYeq | ⟨-, ⟨eSL⟩, -⟩⟩
  ·
    have hnorm : ((altIHK θ c d).subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff hKX).mpr fun k x hk hx => altIH_conj (hXGs hx) hk
    have hXK : X ≤ altIHK θ c d := by
      have hN : (((altIHK θ c d).subgroupOf X).comap (yuProj X)).Normal := hnorm.comap (yuProj X)
      have h1 := oResidualTwo_eq_top_iff.mp hXcls.1.residual_eq _ hN fun g => ⟨1, by
        show yuProj X (g ^ 2 ^ 1) ∈ (altIHK θ c d).subgroupOf X
        rw [map_pow, Subgroup.mem_subgroupOf, Subgroup.coe_pow, pow_one, pow_two]
        exact altIH_sq hcd (hXGs (yuProj X g).2)⟩
      intro x hx
      obtain ⟨g, hg⟩ := yuProj_surjective X ⟨x, hx⟩
      have hmem : g ∈ ((altIHK θ c d).subgroupOf X).comap (yuProj X) := by
        rw [h1]
        trivial
      rw [Subgroup.mem_comap, hg] at hmem
      exact hmem
    have hXeq : X = altIHK θ c d := le_antisymm hXK hKX
    rw [hXeq] at hXcls
    obtain ⟨θK, hnat⟩ := natSection_of_classX_alt hV (altIHK_perfect hcd hn7) hXcls (by omega)
      (hodd.add_even even_two) (altIHK_equiv hcd)
    exact ⟨altIHK θ c d, θK, altIHK_le, altIHK_map, hnat⟩
  ·
    exfalso
    have hKY : altIHK θ c d ≤ Y := by
      rw [hYeq]
      exact hKX
    have h1 := Subgroup.card_le_of_le hKY
    rw [hcardK, hcardY] at h1
    have h2m : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h2m2 : 2 ∣ (m + 2).factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h3 : m.factorial < (m + 2).factorial := (Nat.factorial_lt (by omega)).mpr (by omega)
    omega
  ·
    exfalso
    have h1 : Nat.card ↥Y = 2 ^ k * (2 ^ (2 * k) - 1) := by
      rw [Nat.card_congr eSL.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
        GaloisField.card 2 k (by omega), ← pow_mul, mul_comm k 2]
    exact card_alt_ne_card_sl2 hm hk2 ((Nat.card_congr ε.toEquiv).symm.trans h1)

end CFSG.CGT.PushingUpLit.CGT6
